# DESIGN: `Effect::PipelinedSend` semantics, runtime, and AIR

Status: design draft, implementation pending.
Audience: someone implementing the AIR variant, executor arm, and wire path.

## 1. Purpose and prior art

`Effect::PipelinedSend` is the on-the-wire and in-circuit representation of an
**E-style eventual send to a promise**. In the OCapN tradition (the modern
descendant of E and the Spritely Goblins protocol family) this is the central
move that makes capability systems usable across a network: rather than waiting
for a promise `P` to resolve before sending it a message, you send the message
*now*, addressed to `P`, and the receiving vat queues the message against `P`'s
answer position. When `P` resolves to some object `O`, the queue is drained
into `O`'s inbox. The OCapN draft spec [^captp] calls this `op:deliver` with a
non-false `answer-pos`, and the descriptor used to reference an unresolved
position is `desc:answer N`. The canonical illustration is the
"car factory" example from the spec:

```
<op:deliver <desc:export 5>  ['make-car-factory] 3 false>
<op:deliver <desc:answer 3>  ['make-car]         4 false>
<op:deliver <desc:answer 4>  ['drive]            5 <desc:import-object 17>>
```

Three messages, one network round trip. The receiver sees the second message
land before the first has produced its result and *queues* it against
answer-pos 3, which will be the make-car-factory's return promise. Same for the
third against answer-pos 4. Resolution drives the cascade.

The user's framing — "proving the operation of a pipelined send is asserting
to some mutations of *someone's* data structure" — is exactly right. The
mutation is the **enqueue against the promise's pipeline buffer** (or the
resolved object's inbox). The proof attests to that enqueue.

In dregg's existing scaffolding:

- `captp/src/pipeline.rs` implements the runtime registry: `PipelineRegistry`,
  `PipelinedMessage`, `PipelineWireMessage::PipelineToPromise`. This is the
  un-proven, in-memory machinery — it handles resolution, breakage cascade,
  and chain construction. It is approximately the right shape.
- `turn/src/eventual.rs` defines `EventualRef { source_turn, output_slot }` — a
  *content-addressed* promise handle, where the promise identity is the hash
  of the turn that will produce it. This is more rigorous than OCapN's
  monotonically-increasing answer positions; it gives us free deduplication
  and lets us name promises before either side has issued a request.
- `turn/src/action.rs:409` already has the `Effect::PipelinedSend` variant.
- `turn/src/executor.rs:5274` currently errors when this effect reaches
  `apply_effect`. The comment is right that — *inside a synchronous pipeline*
  — `resolve_turn` should rewrite it away before reaching the executor.
- `circuit/src/effect_vm.rs` has AIR slots for the CapTP family
  (`ExportSturdyRef`, `EnlivenRef`, `DropRef`, `ValidateHandoff`) and the
  queue family (`EnqueueMessage`, `DequeueMessage`, …). PipelinedSend has no
  selector and no constraint — it lives only as a runtime concept.

What's missing is the **asynchronous case**: pipelining a message to a
promise that *cannot* be resolved within the local turn-batch. That is the
case OCapN cares about. That is the case we need a real AIR for.

## 2. Two distinct shapes — keep them distinct

The naïve reading of `Effect::PipelinedSend` conflates two operations that
have different semantics, different state mutations, and *should be different
AIR variants*:

**Shape A — Synchronous pipeline (already exists).** A `Pipeline` is a batch
of turns submitted together. `EventualRef` names the output of a later turn.
The batch executor's `resolve_turn` (executor.rs:7303) rewrites
`PipelinedSend { target: EventualRef, action }` into a fresh root action with
a concrete `CellId` once the producing turn commits. *This is not pipelining
in the OCapN sense* — it's batched topological execution with forward
references, comparable to a Datalog with stratified evaluation. No proof
obligation is owed beyond the proofs of the unfolded effects; the
`EventualRef → CellId` rewrite is verifier-checkable from the receipt and
needs no dedicated AIR variant. Leave this path alone. The current error in
`apply_effect` is the right behaviour: if a PipelinedSend reaches the
executor unresolved, something is wrong with the pipeline scheduler.

**Shape B — Asynchronous eventual send to a promise (new).** The producing
turn is *not in this batch* — it lives on a remote cell, possibly on a remote
federation, possibly not yet scheduled. The sender wants to commit a turn now
that says: "send `m(args)` to whatever P resolves to." The local proof
attests to **what the sender wrote into the pipeline buffer**. The remote
side, separately, proves the delivery when P resolves.

The rest of this document is about Shape B. Shape A is just renamed and
documented away.

## 3. Semantic specification (Shape B)

Given:

- A **sender cell** `S` (this turn's actor).
- A **promise handle** `P` (an `EventualRef`, possibly remote).
- A **method selector** `m` (a stable identifier — content-addressed hash of a
  method name or a CellProgram entry point).
- An **argument blob** `args` (opaque bytes, hashed for the proof).
- An optional **result-promise handle** `R` (where the eventual reply lands).

The effect's meaning is:

> The sender enqueues the message `(m, args)` against the pipeline buffer for
> `P`. If `P` is already known-resolved to a concrete cell `C`, the message
> is instead enqueued against `C`'s inbox. The sender's state is updated to
> reflect the message having been issued (nonce increment, sequence-number
> bump, optional deposit debit). A wire message is emitted carrying
> `(P, m, args_hash, R, sender_sig)` if `P` is remote.

The proof obligation is:

1. The sender holds a capability authorizing `m` against `P` — specifically,
   against `P` as a promise (not `P`'s eventual resolution). Holding a
   capability *to a promise* is itself a first-class right in OCapN; it is
   the bearer's right to be a sender on that answer position.
2. The pipeline buffer (or inbox) accumulator transitioned from `root_old` to
   `root_new` by appending exactly `hash(m, args_hash, seq, sender)`.
3. The sender's sequence number for `P` advanced monotonically.
4. The optional deposit was debited from the sender's balance.

## 4. State mutations, end to end

### Sender side (the cell executing this turn)

- `state.fields[OUTBOX_ROOT_SLOT]` (one of the eight field slots, by
  convention `field[3]`): updated from `old_outbox_root` to
  `hash_2_to_1(old_outbox_root, message_hash)`. This is the sender's
  outbound-pipeline accumulator — a hash chain of every pipelined message
  this cell has ever sent. It is the cell's *proof of having sent*.
- `state.nonce += 1`.
- `state.balance -= deposit` (mirrors `EnqueueMessage`; covers the recipient's
  storage cost. Zero deposit is permitted when the recipient is local and
  the queue is unbounded.)
- Capability root unchanged.

### Recipient side (the cell that owns `P`'s answer position)

When the wire message arrives at the recipient federation, **a separate turn
is issued** by the recipient's executor to absorb the message. That turn's
effect is an `EnqueueMessage` against the recipient's pipeline-buffer queue
for `P` (with the program VK pinned to the swiss/promise identity). This is
already a well-defined AIR variant. The pipelined-send AIR variant on the
*sender* side does not directly prove the recipient's enqueue; it proves that
the sender legitimately emitted a message that **commits** the recipient to
enqueue. Federation cross-checking (or a handoff certificate, or a
`ValidateHandoff`-style witness) closes the loop.

### Network side

A `PipelineWireMessage::PipelineToPromise` is emitted. Its payload includes
the sender's signature over `(P, m, args_hash, R, sender_seq)` and the
sender's turn receipt hash, which transitively contains the
`PipelinedSend` effect hash. The recipient can verify the sender's STARK
proof and the signature before accepting the enqueue.

### Resolved case

If `P` is already resolved in the sender's local `PipelineRegistry`
(i.e. the sender previously saw a `PromiseResolved` for `P`), the executor
**rewrites** the effect to a direct `EnqueueMessage` against the resolved
cell's inbox queue. The proof in this case is the standard `EnqueueMessage`
proof, but with one extra binding: the enqueue must attest that the
resolution was *seen* — by including the resolved cell ID and a witness that
the resolution claim is anchored in the federation's history.

## 5. AIR design

I propose **one variant**, `PIPELINED_SEND`, selector index `24` (continuing
the existing numbering). The `resolved: bool` is encoded as a parameter bit
that selects between two constraint conjunctions, both of which gate on the
same selector. Keeping it as one selector avoids the lookup-argument overhead
of two near-identical AIRs and is consistent with how `EnqueueMessage`
already handles the optional program-VK branch via a multiplicative selector
inside its constraint group.

### Selector

```
pub const PIPELINED_SEND: usize = 24;
```

Update `NUM_EFFECTS = 25` and the corresponding `EffectMask` bit in
`cell/src/facet.rs`. Mask placement: same group as `EFFECT_INTRODUCE`
(capability-transfer-like effects).

### Parameters (8 slots available)

| Slot | Name                       | Meaning                                                                    |
|------|----------------------------|----------------------------------------------------------------------------|
| 0    | `PIPELINE_PROMISE_ID`      | Promise handle hash: `hash(source_turn_hash, output_slot)` as a BabyBear.  |
| 1    | `PIPELINE_METHOD_SELECTOR` | Hash of method name / VK of the CellProgram method to invoke.              |
| 2    | `PIPELINE_ARGS_HASH`       | BLAKE3-then-baby-bear of the args blob.                                    |
| 3    | `PIPELINE_RESULT_PROMISE`  | Hash of the result-promise EventualRef, or ZERO if fire-and-forget.        |
| 4    | `PIPELINE_DEPOSIT`         | Sender deposit (BabyBear). Mirrors `ENQUEUE_DEPOSIT`.                      |
| 5    | `PIPELINE_SEQ`             | Sender's per-promise sequence number, pre-increment.                       |
| 6    | `PIPELINE_RESOLVED_CELL`   | Resolved cell ID if known, else ZERO. Activates the resolved branch.       |
| 7    | `PIPELINE_RESOLVED_INV`    | Inverse of `PIPELINE_RESOLVED_CELL` if non-zero, else zero (branch gate).  |

The branch gate (slot 7) works the same way the queue-program-VK gate works in
`EnqueueMessage`: `(1 - resolved_cell * resolved_inv)` is the "unresolved"
indicator (zero iff resolved_cell != 0). This costs one multiplication per
row and avoids a second selector column.

### Aux columns (need 5)

| Aux | Meaning                                                                        |
|-----|--------------------------------------------------------------------------------|
| 0   | `message_hash = hash(method, hash(args_hash, hash(seq, sender)))`              |
| 1   | `new_outbox_root = hash(old_outbox_root, message_hash)` (unresolved branch)    |
| 2   | `new_inbox_root  = hash(old_inbox_root,  message_hash)` (resolved branch)      |
| 3   | `promise_binding = hash(promise_id, method_selector)` — capability check witness |
| 4   | `cap_membership  = hash(promise_binding, old_cap_root)` — membership in cap root |

### State columns touched

- **Unresolved branch** (`(1 - resolved_cell * resolved_inv) == 1`):
  - `field[3]` (sender outbox root) transitions: `new == hash(old, message_hash)`.
  - `field[4]` (queue/inbox root) **unchanged**.
- **Resolved branch** (`resolved_cell * resolved_inv == 1`):
  - `field[3]` (sender outbox root) **unchanged**.
  - `field[4]` (recipient inbox root, in the rewritten direct-delivery case)
    transitions: `new == hash(old, message_hash)`.
  - The `resolved_cell` parameter must equal a cell ID encoded in the
    `OUTPUTS` PI (so the verifier can check resolution provenance).
- Common to both branches:
  - `balance_lo` debited by `PIPELINE_DEPOSIT` (mirrors `EnqueueMessage`).
  - `nonce` increments by 1.
  - `cap_root` unchanged (we are using a capability, not granting one).
  - All other fields unchanged.

### Constraints

Let `s = local[sel::PIPELINED_SEND]`, `resolved_cell = local[PARAM_BASE + 6]`,
`resolved_inv = local[PARAM_BASE + 7]`. Let
`is_unresolved = ONE - resolved_cell * resolved_inv` and
`is_resolved   = resolved_cell * resolved_inv`. Both factors are forced to
0/1 by the cross-constraint
`s * resolved_cell * (resolved_cell * resolved_inv - ONE) == 0`
(this is the standard "zero or inverse" trick used by `DropRef` and the
program-VK gate).

```
C1 (always): s * (aux[0] - hash(method, hash(args_hash, hash(seq, sender_id)))) == 0
C2 (always): s * (aux[3] - hash(promise_id, method_selector)) == 0
C3 (always): s * (aux[4] - hash(aux[3], old_cap_root)) == 0
   // C3 binds: prover claims that promise_binding is a leaf in the sender's
   // cap_root. The actual Merkle path is supplied via aux[5..] in a separate
   // sub-AIR (re-use the existing `merkle_air` membership proof) — analogous
   // to how `ValidateHandoff` uses `aux[0] = hash(cert_hash, approved_set_root)`
   // and assumes the verifier chains it.
C4 (always): s * (new_bal_lo - old_bal_lo + deposit) == 0
C5 (always): s * (new_bal_hi - old_bal_hi) == 0
C6 (always): s * (new_nonce - old_nonce - ONE) == 0
C7 (always): s * (new_cap_root - old_cap_root) == 0

// Unresolved branch — proves the SENDER'S outbox grew.
C8:  s * is_unresolved * (aux[1] - hash(old_f3, aux[0])) == 0
C9:  s * is_unresolved * (new_f3 - aux[1]) == 0
C10: s * is_unresolved * (new_f4 - old_f4) == 0          // inbox slot untouched

// Resolved branch — proves the RECIPIENT'S inbox grew (direct delivery).
C11: s * is_resolved * (aux[2] - hash(old_f4, aux[0])) == 0
C12: s * is_resolved * (new_f4 - aux[2]) == 0
C13: s * is_resolved * (new_f3 - old_f3) == 0            // outbox slot untouched

// Branch gating well-formedness.
C14: s * resolved_cell * (resolved_cell * resolved_inv - ONE) == 0
   // either resolved_cell == 0 (unresolved), or it has a valid inverse.

// Sequence monotonicity (cross-row, but for a single-effect row we treat as
// boundary: the executor includes prev_seq in args and the runtime feeds
// seq = prev_seq + 1, witness-checked here).
C15: s * (PIPELINE_SEQ - prev_seq_for_promise - ONE) == 0
   // prev_seq_for_promise is sourced from aux[?]; see "Sequence tracking" below.
```

Other fields (`fields[0..3] except 3`, `fields[5..8]`) are constrained unchanged
under `s`, the same way every other variant constrains its untouched fields.

### Public inputs

Add to the `pi` module:

```
PIPELINE_PROMISE_ID    // exported so cross-federation verifier can match
PIPELINE_MESSAGE_HASH  // == aux[0] on the row, exposed for outbound binding
```

`PIPELINE_MESSAGE_HASH` is the value the wire layer signs and the recipient
federation cross-checks against the `EnqueueMessage` proof it generates when
ingesting the message.

### Sequence tracking

The sender needs per-promise sequence numbers to prevent replay and to give
the recipient a total order on this sender's messages to this promise. Two
options:

1. **Dedicated state slot**: reserve `field[6]` as a "per-cell pipeline
   sequence root" — a small Merkle root over `(promise_id -> seq)` for every
   promise this cell currently has outstanding messages for. C15 then requires
   a membership proof in `field[6]` plus a root transition.
2. **Implicit via outbox root**: since the outbox root is a hash chain over
   `(seq, ...)`, replay is impossible if the prover commits to `seq` from
   `aux` — but a malicious sender could reorder freely. Probably acceptable
   for v1, since the recipient can re-order on receive.

Recommendation: ship v1 with option 2 (sequence is supplied by the prover
and bound into `message_hash`, but not separately checked for monotonicity),
and add option 1 in a v2 once we want strict per-promise ordering.

## 6. Relationship to existing AIR variants

| AIR variant       | Shape                                | Diff from PipelinedSend                                  |
|-------------------|--------------------------------------|----------------------------------------------------------|
| `EnqueueMessage`  | Append to queue, debit deposit       | `EnqueueMessage` is the **recipient-side** proof. `PipelinedSend` is the **sender-side** proof of an outbound message; in the resolved branch it degenerates to (essentially) an `EnqueueMessage` against the recipient's inbox. The two are dual.  |
| `GrantCapability` | Add capability entry to cap_root     | `PipelinedSend` does not modify cap_root. It *uses* a capability (membership-checks it) but does not grant.                                                                                                                                       |
| `Introduce`       | Capability transfer between cells    | `Introduce` moves a right; `PipelinedSend` exercises an existing right.                                                                                                                                                                            |
| `ExportSturdyRef` | Mint swiss-numbered routing entry    | `ExportSturdyRef` creates a promise-like handle (a durable cap URL). `PipelinedSend` sends a message *to* such a handle.                                                                                                                           |
| `ValidateHandoff` | Membership in approved-cert set      | Closest structural analog: both check membership in a root, both touch nothing on the cell beyond cap_root / outbox_root. PipelinedSend's C3+C4 are modeled after ValidateHandoff's aux[0].                                                        |
| `EnlivenRef`      | Validate swiss exists, bump use_count| PipelinedSend's "resolved branch" is roughly EnlivenRef + EnqueueMessage composed.                                                                                                                                                                  |

The mental model: **`PipelinedSend` is `EnqueueMessage` with capability-check
attached and a branch for direct-vs-buffered delivery.**

## 7. Runtime data structures (turn/src/)

Augment `turn/src/eventual.rs` and `turn/src/executor.rs` as follows. The
synchronous-Shape-A path stays; we add an asynchronous-Shape-B path that
*actually applies* the effect to ledger state.

### New runtime types

In `turn/src/pending.rs` (or a new `turn/src/promise.rs`):

```rust
/// A promise the local executor knows about. Either it's resolved (we have
/// the cell ID), broken (with a reason), or pending (with a queue of
/// outbound messages we've committed to sending once resolution arrives).
pub enum PromiseRecord {
    Pending {
        promise_id: EventualRef,
        owner_federation: Option<FederationId>, // None = local
        outbound_queue: Vec<MessageHash>,
        next_seq: u64,
    },
    Resolved {
        promise_id: EventualRef,
        cell: CellId,
        resolved_at_height: u64,
    },
    Broken {
        promise_id: EventualRef,
        reason: String,
    },
}

/// Per-cell state appended to the cell's `field[3]` (outbox root).
/// The actual storage is a content-addressed Merkle-ish accumulator; this is
/// just the in-memory mirror.
pub struct OutboxJournal {
    pub messages: Vec<PipelinedMessageRecord>,
}

pub struct PipelinedMessageRecord {
    pub promise_id_hash: [u8; 32],
    pub method: [u8; 32],
    pub args_hash: [u8; 32],
    pub seq: u64,
    pub result_promise: Option<EventualRef>,
}
```

### Executor arm

Replace executor.rs:5274 with:

```rust
Effect::PipelinedSend { target, action } => {
    // 1. Check capability: the actor must hold a cap authorizing
    //    `action.method` against `target` as a promise.
    self.check_promise_capability(actor, target, &action, ledger, path)?;

    // 2. Look up promise state in the promise registry. If resolved → goto 5.
    let promise_state = self.promises.lookup(target);

    // 3. UNRESOLVED branch.
    let message_hash = compute_message_hash(target, &action, seq, actor);
    let sender_cell = ledger.get_mut(actor).ok_or(...)?;
    let old_outbox = sender_cell.fields[OUTBOX_SLOT];
    sender_cell.fields[OUTBOX_SLOT] = poseidon_2to1(old_outbox, message_hash);
    sender_cell.balance -= deposit;
    sender_cell.nonce += 1;
    journal.record_pipelined_send(actor, *target, message_hash);

    // 4. Emit wire message via the pipeline bridge.
    self.pipeline_bridge.enqueue_outbound(target, action, ...);
    return Ok(());

    // 5. RESOLVED branch.
    let resolved_cell = match promise_state { Resolved { cell, .. } => cell, ... };
    // Direct-deliver to resolved_cell's inbox queue (this is now equivalent
    // to an EnqueueMessage against resolved_cell's pipeline queue).
    self.apply_effect(
        Effect::EnqueueMessage { /* against resolved_cell */ ... },
        ledger, path, &resolved_cell, actor, journal,
    )?;
}
```

The capability check at step 1 is the crux of soundness: see §8.

### Hash binding

`Effect::PipelinedSend::hash()` is already implemented at action.rs:968. It
covers `(target.source_turn, target.output_slot, action.hash())`. Verify that
this covers everything the AIR's PI binds — specifically that `method_selector`
and `args_hash` are reachable from `action.hash()`. They are, transitively.

## 8. Adversarial considerations

### (a) Can the sender pipeline to a promise they don't hold?

This is the most important question. In OCapN, the right to send to an
answer position is *implicit* — anyone who knows the answer position number
can send to it. That works in OCapN because answer positions are scoped
per-session and only the session participants know them. In dregg,
`EventualRef` is content-addressed and globally derivable from a turn hash;
anyone who watches the chain can construct one. So we **must** require an
explicit capability.

The capability is: holding a "send-to" right against `(promise_id, method)`,
encoded as an entry in the sender cell's `cap_root`. The right is granted in
one of three ways:

1. **By the promise originator at issuance.** When a cell creates an
   EventualRef (e.g., by submitting a turn that will return a value), the
   originator emits a `GrantCapability` granting send-rights to itself.
   For collaborative pipelines, the originator may grant to others via
   `Introduce`.
2. **By a chain step.** When a sender pipelines step N+1 whose target is the
   result-promise of step N, the very act of issuing step N (with a
   non-None `result_promise_id`) implicitly grants the sender send-rights
   to that result. This must be enforced by `apply_effect` for the step-N
   effect: it must call `GrantCapability(actor, result_promise_ref, ...)`.
3. **By handoff certificate.** A `desc:handoff-give`-style transfer.

C2/C3/C4 in the AIR (the `promise_binding ∈ cap_root` Merkle check) attests
that the cap is present. The verifier can audit it independently.

### (b) Can a sender drain a recipient's inbox?

This is the OCapN "Sybil resistance for promises" question. Mitigation:

- **Storage deposit** (`PIPELINE_DEPOSIT`, parameter slot 4) is debited from
  the sender's balance per message. Same mechanism `EnqueueMessage` uses.
  The recipient sets the per-promise deposit when it creates the promise
  (in v1, hard-coded to the cell's queue cost-per-slot; in v2, declared in
  the promise issuance).
- **Promise-scoped capability**: even with a deposit, the sender can't pile
  on messages without holding the cap, so the recipient controls who can
  pipeline at all.
- **Capacity bound on pipeline buffers**: each promise has a max buffer
  length, declared at promise issuance and stored as field metadata. The
  AIR cannot enforce this directly (we don't expose per-promise capacities
  on the state row), so it's enforced in the executor pre-check, with a
  separate `quantified_absence` AIR proving "the queue length is below the
  cap." Out of scope for v1.

### (c) Can a recipient repudiate having received the pipelined message?

In the unresolved branch, no — the *sender's* proof shows the sender
appended `message_hash` to their outbox root. The wire message carries this
proof plus a signature. When the promise resolves and the recipient must
deliver, the recipient owes its own `EnqueueMessage` proof against its
inbox. Failure to produce that proof is observable (the recipient's promise
buffer is non-existent or doesn't contain the expected hash chain).
Refusal-to-enqueue is detectable; refusal-to-deliver-on-resolution becomes a
breakage event (§(d)).

In the resolved branch, the recipient *is* the executor of the
PipelinedSend, so non-repudiation is the same as for any other effect.

### (d) What happens on promise resolution failure?

The existing `PipelineRegistry::break_promise` already cascades. From the
proof side: a broken promise generates a `PromiseBroken` wire message. The
sender, upon receiving it, owes a *cleanup* turn that drains its outbox
journal for that promise (or marks the relevant entries as void). This
cleanup turn is itself proven (it's effectively a DropRef-style effect
against the promise's outbox accumulator). We don't need a new AIR variant
for this; reuse `DropRef`-style decrement constraints with appropriate
parameters, or model it as a fold over `EnqueueMessage`/`DequeueMessage`
of the outbox.

If the result-promise of a broken pipeline step has further steps queued
against it (a chain), `break_promise` produces `BrokenPromiseNotification`s
that fan out across federations. Each affected sender must, in turn, clean
up. The current `captp/src/pipeline.rs` already implements this cascade
correctly at the in-memory level; the AIR design above leaves the cleanup
side for a follow-up.

### (e) Replay

Without a per-promise sequence check (§5 "Sequence tracking" option 2), a
malicious sender can build two turns with identical
`(promise_id, method, args_hash)` and submit both. Both will produce
distinct outbox-root transitions (since the chain hash differs by chain
position), but they will be semantically duplicate messages. The recipient
must deduplicate on `message_hash`. v2 closes this by binding sequence into
the AIR.

### (f) Cross-federation forgery

If `P` is remote, the sender's federation cannot directly enqueue into the
remote pipeline buffer. The sender's STARK proof + signature is shipped over
CapTP. The remote federation runs `on_pipeline_message` (which calls
`pipeline_message` in `captp/src/pipeline.rs`), verifies the proof + sig,
and issues its own `EnqueueMessage` turn to absorb the message. This is the
same trust pattern as cross-federation bridges already use, modulo the
pipeline-buffer being a per-promise queue rather than a per-federation
balance account.

## 9. Implementation order

1. Add `PIPELINED_SEND` selector + parameters + constraints to
   `circuit/src/effect_vm.rs`. Mirror the structure of `EnqueueMessage`
   (it's the closest sibling) plus the `is_resolved`/`is_unresolved` gating
   from `DropRef`'s zero-or-inverse pattern.
2. Reserve `field[3]` as `OUTBOX_ROOT` in the cell state convention. Update
   `dregg_cell` documentation and any cell-init code that touches field[3].
3. Wire `Effect::PipelinedSend` into `Effect::air_selector_index`
   (effect_vm.rs:2670-ish) → `sel::PIPELINED_SEND`.
4. Add the witness-row writer in the `Effect::apply_to_row` loop (the giant
   match around effect_vm.rs:2840-3020).
5. Replace `apply_effect`'s `Effect::PipelinedSend` error arm
   (executor.rs:5274) with the implementation in §7. Behind a feature flag
   if you want; default-on once the AIR ships.
6. Add the promise registry (`turn/src/promise.rs`) and thread it through
   `TurnExecutor::new`.
7. Add the wire integration: hook the executor into
   `CrossFedPipelineBridge`'s outbox so emitted `PipelineWireMessage`s
   carry the sender's turn-receipt hash and the new
   `PIPELINE_MESSAGE_HASH` PI.
8. Adversarial tests: unauthorized pipeline (no cap held) must fail;
   duplicate sequence number must fail (once v2 lands); resolved-branch
   with wrong resolved_cell must fail; over-spent deposit must fail.
9. Soundness tests in `circuit/src/soundness_tests.rs`: prove constraints
   fire on bit-flips in `aux[0..4]`, in `new_f3`/`new_f4`, in `balance_lo`,
   in `resolved_inv`.

## 10. Open questions for the implementer

- Where exactly to source `prev_seq_for_promise` from for C15. If we go with
  option 2 (no monotonicity check), C15 disappears.
- The Merkle-membership chain for `promise_binding ∈ cap_root` reuses the
  existing `merkle_air` infrastructure. Confirm column-layout compatibility
  in a quick prototype before locking in the aux layout.
- Whether the resolved-branch should consume the entry from the outbox
  accumulator (i.e. transition outbox root *back* by hashing the message out
  of it) or whether the resolved branch is a pure replacement for an
  unresolved one. My recommendation: keep them disjoint (one or the other,
  not both), and let cleanup-of-outbox-on-resolution be a separate effect.

## References

[^captp]: OCapN CapTP draft specification.
  <https://github.com/ocapn/ocapn/blob/main/draft-specifications/CapTP%20Specification.md>
  Sections "Promise pipelining", "op:deliver" (`answer-pos`, `desc:answer`),
  "op:listen", and "Promise and Resolver Objects". The car-factory example
  in §"Promise pipelining by example" is the canonical illustration.

Other prior art consulted while writing this:

- E language documentation, in particular Mark S. Miller's "Robust
  Composition" dissertation (the original reference for promise pipelining
  and the "near references" / "far references" / "vat" model).
- Spritely Goblins documentation on actor model and capability transport
  (the modern OCapN-aligned implementation in Scheme).
- Existing in-repo: `captp/src/pipeline.rs` (the runtime registry, well
  factored — most of the runtime data flow above is already implemented
  there at the in-memory level), `circuit/src/effect_vm.rs:1819–1896`
  (`EnqueueMessage` constraint group, the structural template),
  `circuit/src/effect_vm.rs:2881–2924` (`DropRef`/`ValidateHandoff`
  constraint patterns for membership and zero-or-inverse gating).
