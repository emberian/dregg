// =============================================================================
// Section 11: Executor Delegation
// =============================================================================

= Executor Delegation <sec-delegation>

== Motivation

Sovereign cells generate their own STARK proofs---but proof generation is computationally expensive. A cell operating on a mobile device, IoT sensor, or resource-constrained environment cannot locally produce proofs in reasonable time. _Executor delegation_ allows cells to outsource proof generation and turn execution to specialized executors while maintaining verifiable correctness.

== The Trust Spectrum

Execution trust in Dragon's Egg exists on a spectrum:

#figure(
  table(
    columns: (auto, auto, auto, auto),
    align: (left, left, left, left),
    table.header([*Level*], [*Model*], [*Latency*], [*Trust Assumption*]),
    [0: Full sovereignty], [Cell generates own proofs], [High (local STARK)], [None],
    [1: Delegated proving], [Cell builds turn, executor proves], [Medium], [Executor sees witness],
    [2: Delegated execution], [Cell specifies intent, executor builds + proves], [Low], [Executor honest about state],
    [3: Custodial], [Executor manages cell state and proves], [Lowest], [Executor is honest],
  ),
  caption: [Execution trust levels. Higher levels trade sovereignty for performance.],
)

The protocol is designed so that levels 1 and 2 can be made _trustless_ via challenge mechanisms: an executor that cheats is detectable and slashable. Level 3 (custodial) is equivalent to traditional hosted services---provided for pragmatic reasons but not the target architecture.

== Client-Executor Protocol

=== Delegation Setup

+ *Client* (resource-constrained cell) selects an executor from the service mesh.
+ Client generates a delegation capability: `cap(execute, cell_id, budget=N, effects=[...])`.
+ Client delegates the attenuated capability to the executor (CapTP handoff).
+ Executor acknowledges and posts a bond (slashable on misbehavior).

=== Turn Submission (Level 1: Delegated Proving)

+ Client constructs the turn locally (effects, witness data).
+ Client encrypts the witness to the executor's X25519 key.
+ Client sends encrypted turn to executor via CapTP.
+ Executor decrypts, generates STARK proof.
+ Executor returns the proof to client.
+ Client verifies the proof locally and submits to the blocklace.

The client retains sovereignty over submission: they verify the proof before committing. The executor cannot forge a proof for an unauthorized state transition (the STARK is sound). The executor CAN learn the witness (privacy trade-off for performance).

=== Turn Submission (Level 2: Delegated Execution)

+ Client sends a high-level intent: "transfer 100 computrons to Bob."
+ Executor constructs the full turn (resolving cell state, building effects).
+ Executor generates the STARK proof.
+ Executor submits the turn to the blocklace on the client's behalf.
+ Client receives the `TurnReceipt` and verifies post-state.

At Level 2, the executor has more autonomy. The challenge mechanism provides safety.

== Batch Proving

Executors amortize proof generation cost by batching multiple clients' turns into a single STARK trace:

=== Batch Construction

$ "batch" = {("turn"_1, "witness"_1), ..., ("turn"_k, "witness"_k)} $

The Effect VM proves all $k$ turns in a single AIR evaluation. Each turn's conservation and authority constraints are independent rows in the trace; the aggregate proof covers all turns simultaneously.

=== Amortized Cost

Single-turn STARK generation costs approximately 64 microseconds. Batch proving amortizes the FRI commitment and Merkle tree construction across $k$ turns:

$ "cost_batch"(k) approx "cost_single" + k times "cost_per_turn" $

where $"cost_per_turn" approx 15 mu s$ (trace extension dominates). A batch of 100 turns costs approximately $64 + 100 times 15 = 1564 mu s$---a $4times$ reduction in per-turn cost versus individual proving.

=== Batch Settlement

The batch proof is submitted as a single commitment to the blocklace. Individual turn receipts are derived from the batch receipt via Merkle inclusion proofs: each client can extract their specific receipt from the batch without seeing other clients' turns.

== Challenge Protocol

The challenge mechanism ensures Level 1--2 delegation remains safe even with a dishonest executor:

=== Challenge Conditions

A client can challenge an executor-submitted turn if:

+ *State mismatch*: The post-state commitment does not match the client's expected state.
+ *Unauthorized effect*: The turn includes effects not covered by the delegation capability.
+ *Budget violation*: The turn's computron cost exceeds the delegated budget.

=== Challenge Flow

+ Client publishes a challenge block to the blocklace, referencing the disputed turn receipt.
+ Challenge includes a bond ($>= "executor_bond" \/ 2$).
+ Executor has $W_"challenge"$ waves (governance-configurable, default 20) to respond.
+ *Executor responds with proof*: STARK proof that the turn satisfies the delegation capability's constraints. If valid: challenger's bond slashed.
+ *Executor fails to respond*: Executor's bond slashed. Turn is reverted (post-state rolled back to pre-state). Client compensated from executor's bond.

=== Revert Semantics

Reverting a challenged turn is possible because:

- The pre-state commitment is recorded in the turn receipt.
- The cell's state is deterministic given inputs.
- Dependent turns (those building on the reverted post-state) are transitively invalidated.

Transitive invalidation is bounded: only turns by the same cell that chain from the reverted turn's post-state are affected. Cross-cell effects that consumed the reverted turn's outputs trigger compensation (from the executor's bond).

== Executor Market

=== Executor Discovery

Executors register in the service mesh (Section 9):

```
{
  "service": "executor",
  "capabilities": ["stark_proving", "batch_100", "level_2"],
  "price": "0.5 computrons/turn",
  "bond": 50000,
  "uptime_sla": "99.9%",
  "location": StrandId(0xef34...)
}
```

=== Pricing Models

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Model*], [*Structure*], [*Use Case*]),
    [Per-turn], [Fixed fee per turn proved], [Occasional users],
    [Subscription], [Monthly fee for $N$ turns], [Regular agents],
    [Batch], [Discounted rate for bulk], [High-throughput applications],
    [Stake-proportional], [Free proving for stakers], [Validator-operated executors],
  ),
  caption: [Executor pricing models. Competition among executors drives prices toward marginal cost.],
)

=== Reputation

Executor reputation is computable from their receipt chain:

- *Uptime*: Fraction of challenge windows where the executor responded successfully.
- *Accuracy*: Zero successful challenges against the executor.
- *Latency*: Median time from turn submission to proof delivery.
- *Bond health*: Current bond / required bond ratio.

Clients query executor reputation via the service mesh before delegating. No trusted reputation oracle---the data is derivable from public receipts.

== Security Properties

*Safety (Level 1)*: A delegated prover cannot forge an invalid proof (STARK soundness). The client verifies before submission. Safety is unconditional.

*Safety (Level 2)*: A delegated executor cannot cause permanent harm---challenges revert invalid turns and slash the executor's bond. Safety holds if challenges are submitted within the window.

*Liveness*: If an executor goes offline, the client can revoke the delegation capability and either prove locally or delegate to another executor. No lock-in.

*Privacy*: Level 1 reveals the witness to the executor. Level 2 reveals the intent. For privacy-sensitive operations, clients should use Level 0 (self-proving). The system supports mixed-level operation: privacy-critical turns are self-proved; routine turns are delegated.
