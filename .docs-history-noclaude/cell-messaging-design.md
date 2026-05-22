# Cell-to-Cell Messaging and Reactive Program Execution

Design exploration for adding inter-cell messaging and on-chain reactivity to pyana.

## Status Quo

Pyana currently implements an **off-chain-first** execution model:

1. **Programs live outside the federation.** AI agents, cloud services, and solvers observe
   state, compute decisions, and submit pre-computed turns (call forests) to the federation.
2. **Turns declare all effects upfront.** There is no dynamic dispatch at execution time.
   The executor validates and applies effects, but does not produce new effects.
3. **CellProgram is purely validating.** It accepts or rejects state transitions via
   `evaluate(new_state, old_state) -> Result<(), ProgramError>`. It never PRODUCES effects.
4. **Reactivity exists, but it's off-chain.** The `PendingTurnRegistry` holds turns awaiting
   conditions (receipt arrival, height reached, proof presentation). The NODE executes them
   when conditions are met -- the cells themselves are inert.

The question: should cells be able to REACT to incoming messages by producing effects,
moving some logic on-chain?

## Design Space

### Option A: Inbox/Mailbox Model

Cells have an ordered inbox. Messages accumulate. The cell's program drains the inbox and
produces effects for each message.

```
Effect::SendMessage { to: CellId, payload: Vec<u8> }

struct Inbox { messages: VecDeque<Message> }
struct Message { from: CellId, payload: Vec<u8>, height: u64 }
```

**Processing model:** When a cell's operator (or the federation itself) submits a "drain"
turn, the cell's program processes pending messages and emits effects.

**Pros:** Simple, familiar (actor model). Messages are durable. Cell can process at its
own pace. No reentrancy -- messages are processed in a separate turn from sending.

**Cons:** Requires storage proportional to pending messages. Who pays for inbox storage?
Latency is high (at least two turns for request/response). The "drain" turn is still
submitted by an external operator unless the federation auto-processes.

### Option B: Callback/Handler Model

Effects can trigger handler functions on target cells (like Ethereum's receive/fallback).
When a turn produces an effect targeting cell B, and B has a handler registered for that
effect type, the handler executes synchronously within the same turn.

```
CellProgram::Handler {
    trigger: Symbol,  // method hash that triggers this handler
    circuit_hash: [u8; 32],  // circuit defining the handler logic
}
```

**Pros:** Low latency -- everything happens in one turn. Simple mental model for the
sender (just target the cell, its handler does the rest).

**Cons:** REENTRANCY. This is the Ethereum model. Cell A calls B's handler, B's handler
calls A's handler, state is inconsistent. Requires reentrancy guards, call-depth limits,
and immense care in handler authoring. Partially defeats the purpose of the capability
model (capabilities mediate access, but handlers bypass the "who calls me" check by
running inside someone else's turn).

### Option C: Event Subscription Model

Cells subscribe to events from other cells. The federation routes matching events to
subscribers, triggering their programs.

```
Effect::Subscribe { source: CellId, topic: Symbol, handler: CellProgram }
Effect::Unsubscribe { source: CellId, topic: Symbol }
```

When a cell emits an event (already exists as `Effect::EmitEvent`), the federation checks
all subscribers and enqueues handler invocations.

**Pros:** Decoupled. Publisher doesn't need to know about subscribers. Natural for
observation patterns (price feeds, state change notifications).

**Cons:** Subscription state is expensive to maintain at federation scale. Fan-out problem:
one event triggers N handlers. Who pays? The publisher didn't consent to N computations.
Creates implicit dependencies that are hard to reason about.

### Option D: Channel Model (seL4-style endpoints)

Persistent bidirectional channels between cell pairs, mediated by capabilities. A channel
is a named, typed conduit. Sending requires holding the send-end capability; receiving is
gated by the receive-end capability.

```
Effect::CreateChannel {
    send_end: CellId,    // who gets the send capability
    recv_end: CellId,    // who gets the receive capability
    channel_type: Symbol, // type tag for the channel
}

Effect::ChannelSend {
    channel: ChannelId,
    payload: Vec<u8>,
}
```

The receive-end cell has a program that processes messages when they arrive.

**Pros:** Capability-mediated (fits pyana's model). No broadcast/fan-out problems. Clear
authorization: you need the send-end cap to send. Pairs well with seal/unseal for
partition-tolerant transfer.

**Cons:** Channel management overhead. Every communication path needs explicit setup.
State explosion if cells communicate with many peers. Doesn't scale to open systems
where you want to receive messages from anyone (you'd need a "public channel" concept
that weakens the capability model).

### Option E: Minimal Queuing (Store-and-Forward) -- RECOMMENDED

Not full smart contracts. Not handlers. Just: **"hold this effect for cell B until B's
operator comes online and processes it."**

```
Effect::Enqueue {
    target: CellId,
    payload: Vec<u8>,
    deadline: u64,       // auto-cancel after this height
    bond: u64,           // computrons locked to pay for storage
}
```

The federation holds the queued message. When cell B's operator submits a turn that
references the queued message, the cell's program validates and produces effects:

```
CellProgram::Reactive {
    /// Constraints that the cell's program VALIDATES (same as Predicate).
    constraints: Vec<StateConstraint>,
    /// Circuit that PRODUCES effects from (current_state, message) -> effects.
    /// The circuit's public inputs include the message hash and current state.
    /// The circuit's public outputs include the resulting state and effect hashes.
    reactor_circuit: [u8; 32],
}
```

The operator submits a turn with:
1. A `DequeueAndProcess` effect referencing the queued message
2. A STARK proof that the reactor_circuit correctly transforms (state + message) into
   the declared effects
3. The actual effects produced by the program

The federation verifies the proof and applies the effects. The AI agent (operator) does
the actual computation off-chain, but the proof guarantees correctness.

**This is email, not phone calls.** Asynchronous, durable, bounded, and the recipient
controls when to process. But with cryptographic enforcement that processing is correct.

## Recommendation for Pyana

**Option E (Minimal Queuing with Reactive Programs)** is the right model. Here's why:

### 1. It preserves off-chain-first

The AI agent remains the executor. It watches for queued messages, computes the correct
response, generates a STARK proof, and submits the result. The federation never executes
arbitrary logic -- it only VERIFIES proofs. This aligns with "home for AI": the AI IS
the off-chain program, and the federation is the verification substrate.

### 2. It avoids reentrancy

Messages are processed in separate turns from sending. There is no synchronous callback.
Cell A sends a message. Later, cell B's operator processes it in a new turn. No shared
state, no re-entrance, no call-depth limits. This is the seL4 model: IPC is asynchronous.

### 3. It composes with existing primitives

- `ConditionalTurn` already models "execute when condition met." A queued message IS a
  condition. The `ResolutionCondition::AwaitMessage` variant is a natural extension.
- `PendingTurnRegistry` already handles cascading resolution. A processed message can
  resolve pending turns waiting for that processing.
- `EmitEvent` already provides observable outputs. A processed message can emit events
  that trigger further off-chain reactions.
- `CellProgram::Circuit` already gates state transitions on proofs. The reactor circuit
  is the same mechanism applied to message processing.

### 4. It handles the key use cases

- **Escrow:** Cell holds funds with a reactor program: "if message proves payment
  delivery, release funds." Neither party needs to be online simultaneously.
- **Automated market maker:** Cell holds liquidity with a reactor: "if message is a valid
  trade at current price, execute swap." The operator (AI agent) processes trades.
- **Delegation enforcement:** Intermediate cell applies policy to forwarded messages
  without the delegator being present. The reactor circuit encodes the policy.
- **Queued operations:** Cell processes messages when its operator comes online. Natural
  for mobile agents with intermittent connectivity.

### 5. It scales with proving technology

As STARK provers get faster (2025: seconds, 2027: real-time), the latency between
"message arrives" and "message is processed" shrinks. Eventually, provers run locally
on the recipient's device and processing is near-instant. But the PROTOCOL doesn't
change -- it's always: enqueue, prove, verify, apply.

## Interaction with Existing Primitives

### PendingTurnRegistry Integration

A queued message creates an implicit pending entry:

```rust
ResolutionCondition::AwaitMessage {
    target_cell: CellId,
    message_hash: [u8; 32],
}
```

When the target cell's operator processes the message (submitting a turn with a proof),
the registry resolves the pending entry. Any turns waiting on "cell B processed message
M" are cascaded.

### ConditionalTurn Integration

The queued message itself can be a `ConditionalTurn`:

```rust
ConditionalTurn {
    turn: /* the enqueue effect */,
    condition: ProofCondition::LocalProof { /* reactor circuit satisfied */ },
    timeout_height: deadline,
}
```

If the reactor isn't proven before the deadline, the message expires and the bond is
burned. This prevents infinite inbox growth.

### EventualRef Integration

The result of processing a message produces `TurnOutput`s that can be referenced by
subsequent pipelined operations:

```rust
Effect::PipelinedSend {
    target: EventualRef { source_turn: processing_turn_hash, output_slot: 0 },
    action: /* follow-up action using the result */,
}
```

### Obligation Integration

The existing `CreateObligation`/`FulfillObligation`/`SlashObligation` pattern works:

1. Sender enqueues message + creates obligation: "recipient MUST process before deadline"
2. Recipient processes message + fulfills obligation
3. If deadline passes without processing, stake is slashed to sender

This creates economic incentive for timely processing without requiring on-chain execution.

## New Types and Effects

### New Effect Variants

```rust
/// Enqueue a message for a target cell's reactive program to process.
Effect::Enqueue {
    /// The cell that will process this message.
    target: CellId,
    /// Opaque payload (interpreted by the reactor circuit).
    payload: Vec<u8>,
    /// Block height after which this message expires and bond is burned.
    deadline: u64,
    /// Computrons locked to cover storage costs until processing or expiry.
    storage_bond: u64,
}

/// Dequeue and process a message, proving correct reactor execution.
Effect::ProcessMessage {
    /// Hash of the queued message being processed.
    message_hash: [u8; 32],
    /// STARK proof that reactor_circuit(state, message) -> (new_state, effects).
    reactor_proof: Vec<u8>,
    /// The effects produced by the reactor (verified against proof public outputs).
    produced_effects: Vec<Effect>,
}
```

### New CellProgram Variant

```rust
CellProgram::Reactive {
    /// Static validation constraints (same as Predicate -- applied to every state change).
    constraints: Vec<StateConstraint>,
    /// Hash of the circuit that defines valid message processing.
    /// Circuit signature: (old_state: [Field; 8], message: [u8]) -> (new_state: [Field; 8], effect_hashes: Vec<[u8; 32]>)
    reactor_circuit_hash: [u8; 32],
    /// Maximum message payload size this cell accepts (bounds storage costs).
    max_message_size: u32,
}
```

### New Resolution Condition

```rust
ResolutionCondition::AwaitProcessing {
    /// The queued message hash being waited on.
    message_hash: [u8; 32],
    /// The cell that needs to process the message.
    target_cell: CellId,
}
```

### Message Queue (per-cell, bounded)

```rust
/// A pending message in a cell's queue.
struct QueuedMessage {
    /// Who sent this message.
    sender: CellId,
    /// Opaque payload for the reactor.
    payload: Vec<u8>,
    /// When this message was enqueued (block height).
    enqueued_at: u64,
    /// When this message expires.
    deadline: u64,
    /// Bond locked by the sender.
    storage_bond: u64,
    /// Content hash (for dequeue reference).
    hash: [u8; 32],
}
```

## Migration Path

### Phase 1: Queuing Without Reactivity (simplest, valuable alone)

Add `Effect::Enqueue` and message queue storage. Messages can be enqueued for any cell.
Processing is still done entirely off-chain: the operator reads the queue, computes the
response, and submits a normal turn. No new CellProgram variant needed.

This already enables: store-and-forward messaging, offline-capable agents, guaranteed
delivery with timeout/bond.

New types: `Effect::Enqueue`, `QueuedMessage`, queue storage in node state.
Effort: Small. Wire up queue storage, add the effect to the executor, add API for reading
the queue.

### Phase 2: Reactive Programs (proven correctness)

Add `CellProgram::Reactive` and `Effect::ProcessMessage`. The operator still does the
computation off-chain, but now the federation verifies (via STARK proof) that the
processing was correct according to the reactor circuit.

This enables: trustless escrow, automated market making, delegation policy enforcement.

New types: `CellProgram::Reactive`, `Effect::ProcessMessage`, reactor circuit verification
in executor.
Effort: Medium. Requires STARK verification infrastructure for arbitrary reactor circuits
(already partially exists via `CellProgram::Circuit`).

### Phase 3: Federation-Assisted Processing (optional, for high-frequency patterns)

For cells with simple reactor programs (predicates, not full circuits), the federation can
process messages automatically without waiting for an external operator. This is the "some
on-chain logic" option -- but only for programs simple enough that the federation can
evaluate them directly.

```rust
CellProgram::AutoReactive {
    constraints: Vec<StateConstraint>,
    // No circuit -- the federation evaluates constraints directly.
    // Limited to simple predicate-based state machines.
}
```

This enables: simple escrows that release when a hash preimage is revealed, rate limiters,
time-locked releases.

Effort: Larger. Requires defining what "simple enough" means, preventing DoS, metering
computation.

## What NOT To Do

### Do NOT implement synchronous callbacks (Ethereum model)

Reentrancy is the single worst design mistake in smart contract platforms. Cell A calls
B's handler, B calls A's handler, A's state is mid-modification. The entire history of
Solidity vulnerabilities (DAO hack, Parity multisig, etc.) flows from this decision.

Pyana's turn model is fundamentally message-passing between isolated objects. PRESERVE
THIS. All inter-cell communication must be asynchronous (different turns, even if the
latency is one block).

### Do NOT add a global event bus

Subscription/fan-out models create implicit coupling, unpredictable gas costs, and
governance nightmares ("who decides what the fan-out limit is?"). Keep communication
point-to-point, mediated by capabilities.

### Do NOT make the federation a general-purpose computer

The federation is an ORDERING and VERIFICATION service, not an execution engine. Keep
computation off-chain. Proofs on-chain. This is pyana's fundamental architectural
advantage over Ethereum: the federation's resource usage is bounded by proof verification
costs, not by arbitrary program execution.

### Do NOT allow unbounded inbox growth

Every queued message must have a deadline and a storage bond. If the bond doesn't cover
storage to deadline, reject the message. If the deadline passes without processing, burn
the bond and delete the message. No free lunch for spammers.

### Do NOT expose raw cell state to message senders

The sender sees only the reactor circuit hash (what the cell DOES), not the cell's current
state. Privacy is preserved: the sender enqueues a message, the reactor processes it, and
the only observable output is the emitted events and state root change. The sender cannot
read field[0..7] of the target cell.

## Summary

The right model for pyana is **asynchronous message queuing with proven-correct reactive
processing**:

1. Messages are enqueued by senders (capability-gated, bond-backed, deadline-bounded)
2. The cell's off-chain operator (AI agent) computes the correct response
3. The operator submits a STARK proof that processing was correct per the reactor circuit
4. The federation verifies the proof and applies the resulting effects
5. Pending turns waiting on the processing are cascadingly resolved

This preserves pyana's off-chain-first philosophy, avoids reentrancy, composes with all
existing primitives (pipelines, conditions, obligations, events), and provides a natural
upgrade path from "simple queuing" to "fully proven reactivity" to "federation-assisted
auto-processing" for simple patterns.

The AI agent remains sovereign. It decides WHEN to process messages and HOW to respond.
The reactor circuit constrains the space of valid responses, not the timing. This is the
"home for AI" model: intelligent off-chain agents backed by cryptographic on-chain
guarantees.
