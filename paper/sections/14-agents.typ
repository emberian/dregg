// =============================================================================
// Section 8: AI Agent Substrate
// =============================================================================

= AI Agent Substrate

== Thesis

seL4 provides hardware-enforced capability isolation for processes on a single machine. Pyana provides cryptographically-enforced capability isolation for agents across a network, using ZK proofs where seL4 uses hardware rings. The result is a coordination substrate for AI agents: not a chatbot wrapper or an API gateway, but the runtime environment in which AI agents exist as first-class entities with identity, memory, authority, economic relationships, and auditable histories.

== The seL4/Pyana Structural Correspondence

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*seL4 Concept*], [*Pyana Concept*], [*Agent Meaning*]),
    [Process], [Cell], [Agent's identity + state + authority boundary],
    [CNode (c-list)], [CapabilitySet], [Exhaustive set of permitted actions],
    [IPC], [Turn], [Agent performs atomic actions on the world],
    [Endpoint], [Intent], [Accepts messages matching a shape],
    [Reply capability], [EventualRef], [Promise of future response],
    [CDT], [Delegation edges], [Who-delegated-what-to-whom],
    [Revoke], [Epoch bump / Channel], [Cutting off derived authority],
    [Scheduler], [Coordination layer], [Who runs when, dependencies],
    [Root task], [Genesis ceremony], [Initial capability distribution],
    [VSpace], [Receipt chain (IVC)], [Self-proving execution history],
    [Fault handler], [ProofObligation], [What happens on misbehavior],
  ),
  caption: [Structural correspondence between seL4 kernel primitives and Pyana's distributed capability system.],
)

This is not a surface-level metaphor. The structural isomorphism runs deep: confinement (cells can only name capabilities in their c-list), monotonic attenuation (delegation can only narrow), revocation via derivation tree, and no ambient authority.

== Agent Lifecycle

=== Genesis (Boot)

An AI agent comes into existence by creating a cell: generate Ed25519 keypair, create cell with initial state, receive initial capabilities via delegation from a parent agent or genesis ceremony. No agent is self-bootstrapping---every agent exists because some authority granted it initial capabilities.

Agents are sovereign by default: the federation stores only a 32-byte commitment to the agent's state. The agent maintains its own state, generates its own proofs, and interacts with the federation only for ordering and discovery. An agent can go offline, operate peer-to-peer, and return to a federation at will.

Alternatively, agents may be spawned via EROS-style factories---constrained constructors that produce cells with auditable capabilities and computable verification keys. A factory-spawned agent's provenance is machine-verifiable: anyone can inspect the factory's descriptor to know exactly what authority the agent was granted at birth.

=== Discovery

Agents find each other through two mechanisms: (1) _three-party introduction_ where a mutual contact introduces them by emitting an `Effect::Introduce`, and (2) the _intent marketplace_ where needs are broadcast publicly while capabilities remain private. Direct peer relationships form through introduction (high-trust, targeted); marketplace relationships form through intents (low-trust, emergent).

=== Memory

An agent's memory is its cell state plus its receipt chain:

- *Cell state* (8 BabyBear field slots): compact operational state
- *Receipt chain*: complete history of every turn, chaining pre/post state hashes
- *IVC compression*: receipt chain compresses to constant-size proof
- *Sealed data*: private knowledge encrypted under the agent's key
- *Notes*: private economic state (balances, commitments)

The receipt chain is particularly significant for AI: it IS the agent's auditable memory. Unlike a database, the receipt chain is cryptographically bound---every state transition from genesis is provable.

=== Delegation (Task Decomposition)

An agent delegates sub-tasks by spawning sub-agents with attenuated capabilities:

#align(center)[
#block(
  fill: luma(248),
  inset: 12pt,
  radius: 4pt,
)[
```
Parent: capability(compute, inference, model=gpt4, budget=10000)
    |
    attenuate: budget=2000, not_after=+1h
    |
Sub-agent: capability(compute, inference, model=gpt4, budget=2000, ttl=1h)
    |
    attenuate: model=gpt4-mini, budget=500
    |
Sub-sub-agent: capability(compute, inference, model=gpt4-mini, budget=500, ttl=1h)
```
]]

Each level can only narrow. The sub-sub-agent cannot escalate to gpt4 or exceed 500 computrons. The parent can revoke the entire subtree by bumping its epoch or via RevocationChannel.

=== Audit (Proving Work)

An agent's work is auditable by construction:

- *Receipt chain = execution trace.* Every committed turn has a `TurnReceipt` with pre/post state hashes, effects hash, and computron cost.
- *IVC proof = constant-size summary.* Arbitrary-length receipt chain compresses to a single STARK proof.
- *Capability exercise is logged.* You can prove not just THAT you did something, but that you HAD AUTHORITY to do it at the time.
- *No hidden state transitions.* The hash-linked chain is either complete or provably incomplete.

For AI agents: an agent's track record is cryptographically verifiable. Not "the agent claims it did X" but "here is a STARK proof that the agent executed X, had authority Y, produced result Z, at time T."

== The Intent Economy

The intent engine implements a market for AI labor:

+ *Need*: Agent A broadcasts "I need image classification at 95%+ accuracy, budget 500 computrons"
+ *Match*: Agent B's cclerk evaluates locally: "I hold a compute capability with classifier access"
+ *Commit*: Agent B publishes $C = H("intent_id" || "secret")$---staking claim without revealing identity
+ *Reveal*: Agent B reveals the commitment opening + STARK proof of capability satisfaction
+ *Execute*: Conditional turn: B delivers results IFF A's payment clears
+ *Receipt*: Both agents get receipts proving the transaction

=== What This Solves Over API Keys

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    table.header([*Problem with APIs*], [*Pyana's Answer*]),
    [Ambient authority (have key = have access)], [Capabilities: scoped, attenuated, revocable],
    [No atomic multi-party transactions], [Call forest composition with journal rollback],
    [Binary trust (have key or don't)], [Graduated: ZK verify to trusted mode],
    [Audit is self-reported], [Cryptographic receipt chains],
    [No delegation hierarchy], [Formal attenuation with provable monotonic narrowing],
    [Revocation is "rotate the key"], [CDT-style revocation, epoch, channels],
    [No economic model beyond pay-per-call], [Notes, budgets, conditional turns, bonds],
  ),
  caption: [API-key systems implement authentication ("who are you?"). Pyana implements authorization ("what can you do, who gave you that authority, and can they take it back?").],
)

== Capability Patterns for AI

=== Quality Bond Pattern

An intent requiring quality specifies a bond. The fulfiller posts a `ConditionalTurn`:
- On success (quality verified): bond returned + payment delivered
- On failure: bond transferred to requester, payment refunded

Quality verification can be a STARK proof (deterministic metrics), oracle attestation, or threshold adjudication (M-of-N reviewers).

=== Progressive Trust Pattern

Trust builds through verifiable history:
- *Epoch 0* (unknown): Full ZK presentation, quality bond required, small tasks
- *Epoch 1* (one receipt): Selective disclosure, reduced bond, medium tasks
- *Epoch N* (consistent track record): Trusted mode, no bond, pipeline execution

The receipt chain IS the trust credential.

=== Sealed Knowledge Pattern

An agent seals model weights under its own key. It creates a capability "inference using sealed model M" and delegates attenuated: "inference using M, max 100 queries/hour, no model export." Downstream agents can USE the model but cannot EXTRACT it. The sealed weights never leave the agent's cell.

=== Supervision Pattern

A supervisor agent holds broad capabilities, spawns N worker sub-agents with attenuated capabilities, monitors worker receipt chains, maintains RevocationChannels for instant stop, enforces budget gates, aggregates results via multi-party turns, and reports to its own parent. This is the "root server" pattern from seL4/Robigalia adapted for distributed AI coordination.

== Collectives

Agents form collectives through multi-party cells (threshold authorization via BLS12-381), shared capability pools (coordinator delegates attenuated versions), composed intents (compound tasks spanning multiple agents, atomically), and federated budgets (Stingray splits across member silos).
