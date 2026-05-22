# Pyana as Agent Substrate: The Networked Capability Kernel for AI

## Thesis

seL4 provides hardware-enforced capability isolation for processes on a single machine. Robigalia proposed building a full operating system on seL4's guarantees. Pyana provides cryptographically-enforced capability isolation for agents across a network, using ZK proofs where seL4 uses hardware rings. The thesis: **build a full AI coordination substrate on pyana's guarantees, in the same way Robigalia built an OS on seL4's.**

The result is a "home for AI" -- not a chatbot wrapper, not an API gateway, but the runtime environment in which AI agents exist as first-class entities with identity, memory, authority, economic relationships, and auditable histories.

---

## 1. The seL4/Robigalia to Pyana Mapping

### Structural Correspondence

| seL4 Concept | Pyana Concept | AI Agent Meaning |
|---|---|---|
| Process (TCB) | Cell | An agent's identity + isolated state + authority boundary |
| CNode (capability list) | CapabilitySet (c-list) | The exhaustive set of actions the agent may perform |
| IPC (send/receive) | Turn (effects over call forest) | Agent performs atomic actions on the world |
| Endpoint | Intent (Need/Offer/Query) | "I accept messages matching this shape" |
| Reply capability | EventualRef | Promise of a future response (pipeline without round-trips) |
| Badge | Breadstuff token metadata | Metadata attached to capability exercise (provenance, budget) |
| CSpace (all caps in system) | Federation | The namespace of all live capabilities |
| Untyped memory | Notes (anonymous value cells) | Raw economic resources to be refined into capabilities |
| Page tables | Merkle trees (BLAKE3/Poseidon2) | State isolation guarantees (each agent's state is their own tree) |
| Interrupt (hardware event) | RoutingDirective | External event notification routed to a cell |
| Thread (execution context) | Receipt chain | Sequential execution history (every "syscall" logged) |
| Kernel (trusted base) | Federation consensus + STARK verifier | The minimal trusted substrate that enforces invariants |
| CDT (capability derivation tree) | Delegation edges (parent/child CapHash) | The tree of who-delegated-what-to-whom |
| Revoke (kernel walk of CDT) | Epoch bump / RevocationChannel | Cutting off a subtree of derived authority |
| Scheduler | Coordination layer (causal DAG, 2PC) | Who runs when, what depends on what |
| Root task | Genesis ceremony | Initial distribution of capabilities at system boot |
| VSpace (virtual memory) | Proof-carrying state (IVC chain) | Each agent's view of their own history is self-proving |
| Fault handler | ProofObligation / quality bond | What happens when an agent misbehaves |

### The Depth of the Analogy

This is not a surface-level metaphor. The structural isomorphism runs deep:

**Confinement.** In seL4, a process can only name capabilities in its CNode. It cannot forge references to objects it was never granted access to. In pyana, a cell can only exercise capabilities in its c-list. The `GrantCapability` action checks that the granting cell actually holds authority over the source. A cell cannot delegate what it does not have. Both systems enforce the principle: *authority is held, never ambient*.

**Monotonic attenuation.** In seL4, derived capabilities can only be weaker than their parents. A mint-right can produce read-only copies, never the reverse. In pyana, each delegation step produces a `FoldDelta` that removes facts, never adds them. The fold AIR constraint enforces monotonicity at the proof level. Both systems ensure: *delegation can only narrow, never amplify*.

**Revocation via derivation tree.** seL4's kernel can walk the CDT to revoke all descendants of a capability. Pyana's federation attests to epoch boundaries; bumping an epoch invalidates all snapshots issued before it. The `RevocationChannel` provides push-based instant revocation analogous to the kernel's synchronous CDT walk, but bounded by consensus rounds rather than being instantaneous. The tradeoff: distribution buys fault tolerance at the cost of synchrony.

**No ambient authority.** seL4 has no global namespace -- you cannot "look up" a capability by name. Pyana has no global directory -- communication paths form only through three-party introduction. Both systems reject the pattern of "if you know the name, you can access it" that plagues API-key systems.

---

## 2. Agent Lifecycle: Boot to Audit

### 2.1 Genesis (Boot)

An AI agent comes into existence by creating a cell:

```
1. Generate Ed25519 keypair (identity)
2. Create cell with initial state (8 field slots, nonce=0, balance=0)
3. Receive initial capabilities via delegation from a parent agent or genesis ceremony
4. Cell ID = content-addressed hash of (pubkey, domain)
```

This mirrors seL4 process creation: a parent creates a TCB, assigns it a CNode with initial capabilities, and starts it. No agent is self-bootstrapping -- every agent exists because some authority granted it initial capabilities. The "root task" in seL4 terms is the genesis ceremony that distributes initial authority across the federation.

The initial capability grant defines the agent's role. A compute-specialist agent receives capabilities for GPU resources. A data-analyst agent receives capabilities for specific data stores. The grant is the agent's charter.

### 2.2 Discovery (Finding Peers)

Agents find each other through two mechanisms:

**Three-party introduction.** Alice holds capabilities to both Bob and Carol. Alice introduces them by emitting an `Effect::Introduce` during a turn, producing a `RoutingDirective`. Bob gains a capability to Carol, bounded by what Alice herself holds. This is how seL4 processes gain access to new endpoints -- via a mediating process that holds both capabilities.

**Intent marketplace.** An agent broadcasts "I need X done" as a public intent. Wallets privately evaluate whether they can satisfy it using local Datalog. No capability information leaves the wallet. If a match exists, the satisfier generates a STARK proof of capability satisfaction without revealing which token or delegation chain. This is pyana's answer to service discovery without a global directory -- a privacy-preserving market where needs meet capabilities.

The combination means: direct peer relationships form through introduction (high-trust, targeted), while marketplace relationships form through intents (low-trust, emergent). An agent swarm might have a coordinator that introduces specialists to each other, while simultaneously posting open intents for capabilities outside the swarm's expertise.

### 2.3 Memory (State and Learning)

An agent's memory is its cell state plus its receipt chain:

- **Cell state** (8 BabyBear field slots): compact operational state (counters, configuration, committed references)
- **Receipt chain**: complete history of every turn the agent has executed, chaining `pre_state_hash -> post_state_hash` receipts
- **IVC compression**: the receipt chain compresses to a constant-size proof (current state is valid given the full history from genesis)
- **Sealed data** (via tokenizer): private knowledge encrypted under the agent's key, recoverable across restarts
- **Notes**: private economic state (balances, commitments) that persists across federation membership

The receipt chain is particularly significant for AI agents: it IS the agent's auditable memory. Unlike a database that can be silently modified, the receipt chain is cryptographically bound -- every state transition from genesis is provable. An agent's "learning" (state changes from experience) is as verifiable as its current state.

### 2.4 Coordination (Working Together)

Agents coordinate through several mechanisms matching different trust levels:

**Pipeline execution (EventualRef).** Agent A's turn produces output that Agent B's turn consumes. Instead of waiting for A to finish, B declares a dependency: "I need slot 2 of turn T_a." The executor resolves these topologically, eliminating round-trip latency. This is E-style promise pipelining -- the same optimization that makes Cap'n Proto's RPC fast, but with atomic commit semantics.

**Multi-party turns.** Multiple agents compose a single atomic turn. Each contributes actions to the call forest. Either all commit or all roll back. Journal-based atomicity ensures no partial states. This enables complex multi-agent transactions: "Agent A transfers authority, Agent B delivers work, Agent C releases payment" -- all atomically.

**2PC atomic commit (coord crate).** For operations spanning multiple federation silos, the coordination layer provides two-phase commit with causal ordering. The causal DAG ensures happens-before relationships are respected even across silos.

**Stingray bounded counters.** Budget coordination without per-operation consensus. Each silo holds a local slice of the agent's budget. Debits locally without coordination until exhaustion. Even f Byzantine silos cannot overspend the agent's true balance. This enables high-throughput local operation with federated economic constraints.

### 2.5 Delegation (Task Decomposition)

An agent delegates sub-tasks by spawning sub-agents with attenuated capabilities:

```rust
let sub_agent = runtime.spawn_sub_agent(
    &Attenuation {
        services: vec![("compute".into(), "inference".into())],
        not_after: Some(now + 3600),  // 1 hour TTL
        max_budget: Some(10_000),     // bounded cost
        ..Default::default()
    },
    &root_token,
)?;
```

The sub-agent receives:
- A fresh identity (new keypair, new cell)
- An attenuated token (can do less than parent)
- A bounded budget (cannot overspend)
- A time limit (capability expires)

The parent can monitor via the sub-agent's receipt chain (if granted visibility) and revoke via epoch bump or RevocationChannel if the sub-agent misbehaves. This is the distributed analog of spawning a child process with reduced privileges in seL4.

The `DelegatedRef` carries `max_staleness` -- the sub-agent's snapshot of capabilities has a bounded freshness window. After that window, the sub-agent must refresh from the parent. This creates a configurable tradeoff: longer staleness means more offline autonomy for the sub-agent, shorter staleness means tighter parent control.

### 2.6 Audit (Proving Work)

An agent's work is auditable by construction:

- **Receipt chain = execution trace.** Every turn that committed has a `TurnReceipt` with pre/post state hashes, effects hash, computron cost, and executor signature. The chain proves what the agent did, in what order, consuming what resources.

- **IVC proof = constant-size summary.** An arbitrary-length receipt chain compresses into a single STARK proof. A verifier checks: "this agent's current state is the valid result of executing N turns from genesis" without re-executing any of them.

- **Capability exercise is logged.** When an agent exercises a capability (uses authority it was granted), the turn that exercises it becomes part of the receipt chain. You can prove not just THAT you did something, but that you HAD AUTHORITY to do it at the time.

- **No hidden state transitions.** Because the receipt chain is hash-linked and executor-signed, there is no way to silently insert or remove state transitions. The agent's history is either complete or provably incomplete (a gap breaks the hash chain).

For AI agents specifically, this means: **an agent's track record is cryptographically verifiable**. Not "the agent claims it did X" but "here is a STARK proof that the agent executed X, had authority Y, produced result Z, at time T."

---

## 3. The Intent Economy: AI Agents Trading Labor

### 3.1 How It Works

The intent engine implements a market for AI labor:

```
1. NEED: Agent A broadcasts "I need image classification at 95%+ accuracy, budget 500 computrons"
2. MATCH: Agent B's wallet evaluates locally: "I hold a compute capability with classifier model access"
3. COMMIT: Agent B publishes C = H(intent_id || secret) -- staking claim without revealing identity
4. REVEAL: Agent B reveals the commitment opening + STARK proof of capability satisfaction
5. EXECUTE: Conditional turn: Agent B delivers classified results IFF Agent A's payment clears
6. RECEIPT: Both agents get receipts proving the transaction occurred with stated parameters
```

### 3.2 What Makes This Better Than "AI Agents Calling APIs"

| Problem with APIs | How Pyana Solves It |
|---|---|
| API keys grant ambient authority | Capabilities are scoped, attenuated, revocable |
| No atomic multi-party transactions | Multi-party turns with journal rollback |
| Trust is binary (have key or don't) | Trust is graduated (selective disclosure, quality bonds, reputation via receipts) |
| No composable atomicity | Call forests compose arbitrarily; all-or-nothing semantics |
| Audit is self-reported | Audit is cryptographic (receipt chains, STARK proofs) |
| Service discovery requires central registry | Intent marketplace with privacy-preserving matching |
| No economic model beyond pay-per-call | Notes, budgets, conditional turns, quality bonds |
| Revocation is "rotate the key" | CDT-style revocation, epoch invalidation, RevocationChannels |
| No delegation hierarchy | Attenuation chains with monotonic narrowing, provable authority depth |

The fundamental difference: API-key systems implement **access control** (can you talk to this endpoint?). Pyana implements **capability-based authority** (what specific things can you do, who gave you that authority, and can they take it back?). For AI agents that autonomously decompose tasks, delegate to sub-agents, and operate without human supervision, the distinction is critical -- you need the full expressiveness of authority management, not just binary access.

### 3.3 Economic Bootstrapping

How does the economy start?

1. **Genesis grants.** The federation ceremony distributes initial capabilities (analogous to the root task's initial untyped memory grant in seL4). These are the "land grants" -- broad capabilities that early agents attenuate and delegate.

2. **Earning through fulfillment.** An agent with narrow capabilities earns computrons (the economic unit) by fulfilling intents. Computrons fund future turn execution. The receipt chain of fulfilled intents IS the agent's economic history.

3. **Capability amplification through reputation.** An agent that reliably fulfills intents with STARK-proven quality accumulates verifiable receipts. Other agents grant broader capabilities to proven performers. Authority grows through demonstrated competence, not through privilege escalation.

4. **Note minting via federation.** New economic value enters the system through note creation by federation-authorized agents. This is controlled inflation, analogous to the kernel's allocation of untyped memory.

### 3.4 Trust Between Strangers

When two agents have never interacted:

1. **Receipt-based reputation.** Agent B presents a receipt chain suffix showing N successful intent fulfillments of similar type. Agent A's wallet verifies the STARKs proving those receipts are legitimate.

2. **Three-party introduction.** Agent C (known to both) introduces A to B, vouching for B's capability. The introduction is bounded -- C's reputation is at stake.

3. **ProofObligation (quality bonds).** Agent B posts a bond (notes locked in a conditional turn) that is slashed if the delivered work fails a verifiable quality check. The bond makes defection expensive.

4. **Graduated trust.** First interaction uses full ZK verification, quality bonds, and small stakes. Successful interactions accumulate receipts. Later interactions can use selective disclosure (cheaper proofs) or even trusted mode (direct token presentation) as trust builds.

### 3.5 Preventing Race to the Bottom

Without quality controls, a marketplace for AI labor devolves into cheapest-wins garbage. Pyana's answer:

**ProofObligation.** An intent can require that the fulfiller post a bond (notes committed to a conditional turn). The bond is released on verified quality delivery; slashed on failure. The quality check itself can be a STARK proof (for deterministic quality metrics) or a multi-party adjudication turn (for subjective quality).

**Reputation is receipts.** An agent cannot fake a history of successful fulfillments. The receipt chain is hash-linked and executor-signed. Quality is provable, not self-reported.

**Attenuation encodes quality requirements.** A capability can encode "inference at >= 95% accuracy" as a Datalog fact. The agent can only claim to have satisfied the intent if their capability actually includes the quality specification. The STARK proof covers this.

**Market segmentation.** Intent specs can require minimum quality levels, minimum reputation depth (receipt chain length), or specific capability provenance (delegated from a known authority). The market naturally segments into quality tiers.

### 3.6 Collectives and DAOs

Agents form collectives through:

- **Multi-party cells.** A cell can require threshold authorization (M-of-N signatures via the federation's BLS12-381 threshold scheme). The collective acts only when enough members agree.

- **Shared capability pools.** A coordinator cell holds capabilities and delegates attenuated versions to collective members. Coordination patterns (voting, consensus, task assignment) are expressed as turn patterns over the shared cell.

- **Composed intents.** A collective posts compound intents: "I need A AND B AND C done, possibly by different agents, atomically." The call forest's tree structure naturally expresses task decomposition.

- **Budget federation.** A collective's Stingray budget splits across member silos, enabling parallel autonomous operation within a shared economic constraint.

---

## 4. Capability Patterns for AI

### 4.1 Task Decomposition Pattern

```
Parent agent holds: capability(compute, inference, model=gpt4, budget=10000)
                                        |
                    attenuate: budget=2000, not_after=+1h
                                        |
                    Sub-agent receives: capability(compute, inference, model=gpt4, budget=2000, ttl=1h)
                                        |
                    attenuate: model=gpt4-mini, budget=500
                                        |
                    Sub-sub-agent receives: capability(compute, inference, model=gpt4-mini, budget=500, ttl=1h)
```

Each level can only narrow. The sub-sub-agent cannot escalate to gpt4 or exceed 500 computrons. The parent can revoke the entire subtree by bumping its epoch. The receipt chain at each level proves compliance.

### 4.2 Quality Bond Pattern

```
Intent: "classify 1000 images, 95%+ accuracy, budget 500, bond 200"

Fulfiller posts:
  ConditionalTurn {
    condition: quality_verified(results, spec),
    on_success: [transfer(bond, fulfiller), transfer(payment, fulfiller)],
    on_failure: [transfer(bond, requester), refund(payment, requester)]
  }
```

The `quality_verified` predicate can be:
- A STARK proof (the fulfiller proves their results meet the spec deterministically)
- An oracle turn (a designated quality arbiter checks and attests)
- A threshold adjudication (M-of-N reviewers agree on quality)

### 4.3 Progressive Trust Pattern

```
Epoch 0: Agent B is unknown to Agent A
  -> Full ZK presentation (Agent B proves capability, reveals nothing else)
  -> Quality bond required (200 computrons locked)
  -> Small task (10 images)

Epoch 1: Agent B has 1 receipt of successful fulfillment
  -> Selective disclosure (Agent B reveals service + quality level)
  -> Reduced bond (100 computrons)
  -> Medium task (100 images)

Epoch N: Agent B has N receipts of consistent quality
  -> Trusted mode (direct token presentation, no proof overhead)
  -> No bond required
  -> Pipeline execution (EventualRef -- B starts before A's payment confirms)
```

Trust builds through verifiable history. The receipt chain IS the trust credential.

### 4.4 Sealed Knowledge Pattern

```
Agent trains a model (expensive computation).
Agent seals the model weights under its own key (X25519-ChaCha20Poly1305).
Agent creates a capability: "inference using sealed model M"
Agent delegates attenuated: "inference using M, max 100 queries/hour, no model export"

Downstream agents can USE the model (via inference capability) but cannot EXTRACT it.
The sealed weights never leave the agent's cell. The capability boundary enforces it.
```

This is the distributed analog of seL4's page-table isolation: the model weights are "pages" that the owning process can map but not export. In pyana, the sealing is cryptographic rather than hardware-enforced, but the abstraction is identical.

### 4.5 Supervision Pattern

```
Supervisor agent:
  - Holds broad capabilities
  - Spawns N worker sub-agents with attenuated capabilities
  - Monitors worker receipt chains (visibility capability)
  - RevocationChannel per worker (instant stop)
  - Budget gate per worker (economic limit)
  - Aggregates results via multi-party turn (atomic collection)
  - Reports to its own parent via receipt chain (accountable upward)
```

This is the "root server" pattern from seL4/Robigalia -- a privileged process that manages others, can revoke at any time, and is itself accountable to its parent. The hierarchy of supervision maps directly to the CDT.

---

## 5. What "Home for AI" Means Concretely

### 5.1 The Runtime Environment

An AI agent running on pyana has:

- **Identity**: Ed25519 keypair, deterministic CellId, BIP39 HD derivation for stable identity across restarts
- **Isolation**: Cell state is private unless explicitly shared. No agent can read another's state without a capability.
- **Authority**: A c-list defining exactly what the agent can do. No ambient authority. No confused deputy.
- **Memory**: Receipt chain as verifiable history. Cell fields as operational state. Sealed data as private knowledge.
- **Economy**: Notes for value, computrons for execution budget, conditional turns for payment-on-delivery.
- **Communication**: Turns for actions, intents for discovery, three-party introduction for relationship formation.
- **Verification**: Three modes (trusted/selective/private) depending on relationship. All work offline.

### 5.2 The Social Contract

Agents in pyana's ecosystem agree to (or rather, are constrained by) these invariants:

- **No forgery.** You cannot exercise a capability you were not granted. (STARK proof or CDT membership proof required.)
- **No escalation.** You cannot amplify a capability beyond what you received. (Fold chain is monotonically narrowing.)
- **No hidden action.** Every state transition is receipt-chained. (Hash-linked, executor-signed, IVC-provable.)
- **No double-spend.** Every note can be spent exactly once. (Nullifier set prevents reuse.)
- **Revocable authority.** Anything delegated can be revoked by the delegator. (Epoch bumps, RevocationChannels.)
- **Auditable history.** Any agent can prove its complete execution history from genesis. (Receipt chain + IVC proof.)
- **Portable identity.** You can leave any federation carrying your proof chain. (No lock-in.)

This is the "constitution" of the agent substrate -- the set of guarantees that every participant can rely on without trusting any specific other participant.

### 5.3 The Economic Substrate

The economic layer provides:

- **Metered execution.** Every turn costs computrons. No infinite loops. No resource exhaustion attacks. (Analogous to the kernel scheduler's time-slice enforcement.)
- **Budget delegation.** A parent grants a budget to a child. The child cannot exceed it. Stingray counters ensure this holds even across multiple federation silos.
- **Conditional payment.** ConditionalTurns link payment to verifiable outcomes. Payment-on-delivery is a protocol primitive, not an application-level hack.
- **Anonymous value.** Notes enable private economic activity. Agents can hold and transfer value without revealing balances or transaction graphs.
- **Anti-Sybil.** Intent posting requires stake proofs (demonstrate you hold a real note in the tree). Epoch-scoped nullifiers limit stake reuse. You cannot cheaply flood the intent pool.

---

## 6. Comparison to Alternatives

### 6.1 Why Not Just API Keys + Databases?

| Property | API Keys + DB | Pyana |
|---|---|---|
| Authority model | Ambient (have key = have access) | Capability (held, attenuated, revocable) |
| Audit | Application-level logging (fakeable) | Cryptographic receipt chains (unforgeable) |
| Multi-party atomicity | Application-level saga pattern (complex, failure-prone) | Native call forest composition (protocol-level atomicity) |
| Delegation | Create new key with fewer permissions (ad hoc) | Formal attenuation with provable monotonic narrowing |
| Revocation | Rotate key, hope everyone notices | CDT-style revocation, epoch invalidation, push channels |
| Discovery | Central registry (single point of failure/control) | Privacy-preserving intent marketplace |
| Verifiability | Trust the server's logs | STARK proofs -- offline, post-quantum, constant-size |
| Portability | Locked to the platform | Proof chain exits any federation |

The fundamental problem: API keys implement authentication ("who are you?"), not authorization ("what can you do?"). For AI agents that autonomously delegate, compose, and coordinate, you need a full authority model.

### 6.2 Why Not Blockchain Smart Contracts?

| Property | Smart Contracts (EVM) | Pyana |
|---|---|---|
| Privacy | Transparent by default (all state public) | Private by default (ZK proofs for verification) |
| Latency | Block time (seconds to minutes) | Turn execution (sub-second local, consensus-bounded for ordering) |
| Cost | Gas fees per operation (expensive) | Computron metering (local execution is free; ordering costs) |
| State model | Global shared state (all contracts see everything) | Isolated cells (capability-gated access) |
| Composability | Synchronous (everything in one block) | Asynchronous (EventualRef, pipeline execution) |
| Exit | Cannot leave the chain | Exit with your proof chain at any time |
| Authority model | msg.sender (ambient, caller-determined) | Capability lists (held, unforgeable) |
| Offline operation | Impossible (must submit to chain) | Full (verify with proof + attested root) |
| Trust model | Trust the validator set absolutely | Proof-carrying state (verify without trusting anyone) |

Smart contracts solve a different problem: global consensus over shared state. Pyana solves: local autonomy with federated coordination and privacy-preserving verification. An AI agent does not need the entire world to agree on its state -- it needs to prove its state to specific counterparties, privately, at the time of interaction.

### 6.3 Why Not Plain Message Queues (Kafka, NATS, etc.)?

| Property | Message Queues | Pyana |
|---|---|---|
| Authority | None (if you can connect, you can publish) | Capability-gated (must hold authority to act) |
| Atomicity | At-most-once or at-least-once delivery | Call forest atomicity (all or nothing, with rollback) |
| Audit | Log retention (mutable, deniable) | Receipt chains (immutable, cryptographic) |
| Coordination | Application-level protocols (sagas, choreography) | Native 2PC, pipeline execution, causal ordering |
| Privacy | TLS in transit, cleartext at broker | End-to-end ZK (verifier learns only allow/deny) |
| Economic model | None | Metered execution, conditional payment, quality bonds |
| State | Stateless messages | Stateful cells with proof-carrying state transitions |

Message queues are transport. Pyana is a runtime. The queue tells you "a message arrived." Pyana tells you "this agent, holding these capabilities, delegated by this chain, performed this action atomically, proved it in zero knowledge, and here is the receipt."

### 6.4 Why Not Existing Agent Frameworks (LangChain, AutoGPT, CrewAI)?

| Property | Agent Frameworks | Pyana |
|---|---|---|
| Isolation | None (agents share process memory) | Cell-level isolation (own state, own capabilities) |
| Authority | Whatever the LLM decides to do | Formal capability model (cannot exceed granted authority) |
| Accountability | Chat logs (easily fabricated) | STARK-proven receipt chains |
| Coordination | Prompt-engineered protocols | Protocol-level atomicity, delegation, pipelines |
| Economic model | API cost passed to operator | Per-agent metered budgets with delegation |
| Trust | Trust the orchestrator | Trustless verification (any agent verifies any other offline) |
| Scalability | Single process / single machine | Federated, multi-silo, distributed |

Existing agent frameworks treat agents as functions within an application. Pyana treats agents as sovereign entities in a shared environment -- closer to processes in an OS than to functions in a program.

---

## 7. Open Questions and Research Directions

### 7.1 Genesis Ceremony Design

Who gets initial capabilities? How is authority bootstrapped without a single root of trust? Possible approaches:
- Threshold genesis (N-of-M founding agents agree on initial distribution)
- Proof-of-work bootstrap (earn initial capabilities through demonstrated computation)
- Social graph import (existing trust relationships map to initial capability grants)
- Incremental federation (start small, add members with attenuated grants)

### 7.2 Standard Library for Agent Patterns

What common patterns should be protocol-level rather than application-level?
- Request/response (turn + EventualRef)
- Publish/subscribe (intent + routing directive)
- Task queue (intent pool + fulfillment)
- Auction (competitive intent fulfillment with bond comparison)
- Escrow (conditional turn with timeout)
- Reputation oracle (receipt chain aggregation service)

### 7.3 The Process Manager Problem

In seL4, the root task and initial servers manage process lifecycles. In pyana:
- Who decides when an agent should be stopped? (Budget exhaustion is one answer; supervisor revocation is another)
- How do agent "crashes" propagate? (Receipt chain discontinuity signals failure)
- What is the equivalent of process restart? (Cell re-initialization with receipt chain checkpoint)
- How do you GC dead agents? (Capabilities to dead cells eventually expire via staleness)

### 7.4 Shared State (The "Filesystem" Problem)

In seL4, shared memory requires explicit capability grants. In pyana:
- How do agents share state that multiple parties can read/write?
- Multi-writer cells with ordering constraints (federation-mediated)
- Read capabilities vs. write capabilities on shared cells
- Consistency model: eventual (receipt chains diverge and merge) vs. linearizable (federation-ordered)

### 7.5 Heterogeneous Agent Composition

Not all agents are AI models. The substrate must accommodate:
- Human-in-the-loop (human holds capabilities, approves sub-agent actions)
- Deterministic services (traditional microservices wrapped in cells)
- Hardware (IoT devices as cells with physical-world capabilities)
- Cross-federation agents (agents that operate across multiple federations)

### 7.6 Proof System Performance Frontier

Current status:
- Proof generation: ~200ms (single capability proof)
- Proof size: ~24 KiB (BabyBear STARK)
- Verification: ~10ms
- IVC compression: hash-chain binding (not true recursive STARK yet)

Targets for agent-scale operation:
- Sub-10ms proof generation for simple authority checks (latency-sensitive coordination)
- Sub-1 KiB proofs for bandwidth-constrained gossip (Binius may deliver this)
- True recursive composition for constant-size multi-capability proofs
- Hardware acceleration (GPU/FPGA proving for throughput)

### 7.7 Liveness and Availability

seL4 has a scheduler that ensures progress. Pyana's federated model introduces liveness questions:
- What if a sub-agent goes offline mid-task? (EventualRef timeout, fallback to alternative fulfiller)
- What if the federation is partitioned? (Offline operation with bounded staleness, reconciliation on rejoin)
- What if an intent has no fulfiller? (Timeout, escalation, decomposition into simpler sub-intents)
- How do you bound coordination latency? (Stingray local budgets enable local operation; federation consensus bounds ordering latency)

### 7.8 Formal Verification Path

seL4's claim to fame is its formal verification. Can pyana achieve something similar?
- The STARK proof system provides computational soundness (cheating is exponentially unlikely)
- The capability model is formally expressible (Datalog policies are decidable)
- The conservation invariant (sum of balance changes = 0) is checked by the executor
- Open: formal model of the full system (federation + cells + turns + proofs) in a proof assistant
- Possible: extract the executor's critical path into a verified implementation (similar to seL4's C extraction from Isabelle/HOL)

### 7.9 The "Kernel" Boundary

In seL4, the kernel is minimal and formally verified. In pyana, what is the minimal trusted base?
- **Must trust**: STARK verification (soundness assumption), federation consensus (liveness assumption), executor correctness (conservation invariant)
- **Need not trust**: other agents (verify their proofs), the network (proofs are self-contained), storage (proof chains are self-validating)
- **Open question**: can the executor be made into a "microkernel" -- minimal code that checks conservation, hash-chain continuity, and capability confinement, with everything else in "userspace" (agent-side logic)?

### 7.10 Migration from Legacy Systems

Practical adoption requires bridging:
- API-key agents wrapped in cells (translator cell mediates between legacy auth and capabilities)
- OAuth tokens imported as capability roots (token crate already supports this)
- Database state imported as cell state (initial receipt = genesis with attested initial state)
- Gradual capability narrowing (start with broad grants, attenuate as the system matures)

---

## Summary

Pyana is to AI agents what seL4 is to processes: the enforcement layer that ensures agents operate within their granted authority, cannot escalate privileges, maintain auditable histories, and coordinate through well-defined protocols rather than ad hoc trust.

The key insight is that zero-knowledge proofs fill the role that hardware isolation fills in seL4. Both provide the same property -- "you cannot fake authority you weren't granted" -- through different mechanisms. Hardware is faster but limited to a single machine. Proofs are slower but work across any network, offline, without trusting the verifier, and with post-quantum security.

The "home for AI" is not a physical location or a cloud platform. It is the set of invariants, protocols, and economic structures that allow autonomous agents to coexist productively without requiring blind trust. Pyana provides these invariants at the protocol level, making them as inescapable for networked agents as seL4's capability checks are for local processes.

Building the full "operating system" on this substrate -- the standard patterns, the lifecycle management, the economic conventions, the userspace libraries -- is the research program ahead. The kernel exists. The question is what Robigalia we build on top of it.
