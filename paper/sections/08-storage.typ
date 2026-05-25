// =============================================================================
// Section 8: Storage as Cell Programs
// =============================================================================

= Storage as Cell Programs <sec-storage-as-cell-programs>

== Thesis: storage primitives are not new Effects

Storage in a distributed capability system differs fundamentally from blockchain state: cells are sovereign (they own their data), storage is metered (ongoing cost, not one-time), and queues are the primary communication primitive (not shared memory). The historically natural framing made each storage primitive a new `Effect` variant: `Effect::QueueAllocate`, `Effect::Enqueue`, `Effect::Dequeue`, `Effect::TopicCreate`, and so on. Each new app proposed new effects; each new effect needed an AIR row, a cost-table entry, a cclerk wrapper, an executor branch. The effect surface bloated; the AIR's column count climbed; the constitution that named effects became harder to govern.

The corrected framing: *storage primitives are not new Effects. They are cell-program patterns.* Compositions of existing `Effect` variants (`SetField`, `EmitEvent`, `Transfer`, `Grant`/`Revoke`, `CreateCellFromFactory`) governed by `CellProgram`s whose `StateConstraint`s are drawn from the 21+ variant slot caveat vocabulary, plus---where genuinely needed---a `WitnessedPredicate` for the witness-attached cases.

Three concrete consequences:

+ *One enforcement loop, not two*: the executor's per-turn evaluator that already runs for every state-modifying turn enforces queue invariants, inbox sequencing, blinded-spend correctness, relay quota. The legacy `QueueConstraint` vocabulary in `storage::programmable` aliases directly to `StateConstraint` post-Lane-G Phase 1.
+ *New primitives plug in by declaring a composition*: no new Effects, no new AIR row, no new cclerk wrapper. The `FactoryDescriptor` carries the slot layout and `state_constraints`; apps use the existing `createFromFactory` cclerk method to instantiate.
+ *Constructor transparency*: anyone with the `factory_vk` can read the descriptor and know exactly what invariants the cell will carry over its lifetime.

== The migration framework

Every storage primitive's migration follows the same six-step pattern:

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    table.header([*Step*], [*Action*]),
    [1. Factory], [Define a `FactoryDescriptor` declaring slot layout + `state_constraints`.],
    [2. Constraints], [Express invariants in `StateConstraint` vocabulary (and `WitnessedPredicate` for witness-attached).],
    [3. App API], [Apps use existing `createFromFactory` + standard `Effect` variants. No new cclerk wrappers.],
    [4. Receipt], [Every modification produces a `TurnReceipt` through the standard executor path.],
    [5. Boundary], [Document the cell's boundary contract per BOUNDARIES.md vocabulary.],
    [6. Deprecate], [The legacy storage-crate enforcement loop becomes a thin re-export of `cell::program::StateConstraint`, or is deleted.],
  ),
  caption: [Six-step migration framework. Each primitive in §3 fills in this pattern.],
)

== Primitives as Cell-Program Patterns

This subsection names the five primary storage primitives and the slot caveat compositions that realize them.

=== CapInbox

A `CapInbox` is a monotonic-sequence, write-once-slot, sender-authorized message queue.

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    table.header([*Slot*], [*StateConstraint*]),
    [`sequence_counter: u64`], [`MonotonicSequence { seq_index }`---the slot's value equals `old[seq_index] + 1` on each enqueue],
    [`messages[N]: MerkleRoot`], [`WriteOnce { index: i }` per slot---each slot is written exactly once, then frozen],
    [`max_messages: u64`], [`FieldLte { i, v: MAX_INBOX_SIZE }`---cell-program-bound upper bound],
    [`sender_set_root: MerkleRoot`], [`SenderAuthorized { set_root_index }`---only members of the cell's allow-list may enqueue],
  ),
  caption: [`CapInbox` slot layout and caveats. No new Effects; no new predicate kinds.],
)

Enqueue: `Effect::SetField { slot: sequence_counter, value: old+1 }` + `Effect::SetField { slot: messages[old], value: msg_hash }` in a single Turn. The two `StateConstraint`s enforce sequencing and write-once-ness; `SenderAuthorized` gates the actor. Dequeue: the recipient cell observes the inbox's state via a read action; consumption advances a per-recipient pointer (also in slots, also `MonotonicSequence`).

=== ProgrammableQueue

The legacy `QueueConstraint` vocabulary (`SenderAuthorized`, `ContentPattern`, `MinDeposit`, `MaxSize`, `RateLimit`, `MonotonicSequence`, `TemporalGate`, `PreimageGate`, `Custom`) is *already* lifted to `StateConstraint` (Phase 1 alias in `storage/src/programmable.rs:30-36`). A `ProgrammableQueue` is simply a cell whose `CellProgram` declares queue-shaped caveats:

- `RateLimit { max_per_epoch, epoch_duration }` for sender throttling.
- `MinDeposit` via `FieldGte` against a sender's deposit slot.
- `TemporalGate { not_before, not_after }` for commit/reveal windows.
- `ContentPattern` via `WitnessedPredicate { kind: Dfa, commitment: pattern_root }` for prefix/regex filtering.

KZG polynomial commitments (`Effect::QueueCommit`) over queue state remain the substrate for constant-size queue proofs and `Dequeue` membership; the difference is that the *invariants* the queue carries (who can enqueue, what fits, when) live in the cell's `CellProgram`, evaluated by the executor, not in a parallel storage-crate loop.

=== PubSubTopic

A `PubSubTopic` is a many-to-many channel: subscribers register a sturdy ref + filter; publishers `Effect::EmitEvent` to the topic's cell; subscribers' cells receive deliveries via CapTP routing. The topic's `CellProgram` declares:

- `SenderAuthorized { set_root_index }`---only publishers in the allow-list may emit.
- A `WitnessedPredicate { kind: Dfa, commitment: topic_filter_root }` per subscriber bound in a slot, gating which messages route to which subscriber.
- `RateLimitBySum { i, max_sum, dur }`---windowed cap on cumulative payload size per publisher.

No new `Effect`; the topic is a cell that holds the subscription tree, and the DFA-as-`WitnessedPredicate` does subscription matching as part of the executor's per-turn evaluation.

=== BlindedQueue

A `BlindedQueue` introduces *one* new `WitnessedPredicateKind`: `Custom { vk_hash: blinded_spend_air_vk }`, the verifier for the spend AIR that proves "I know the commitment opening and the spending key" without revealing the deposit-withdrawal correspondence.

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    table.header([*Slot*], [*StateConstraint*]),
    [`commitment_set_root: MerkleRoot`], [`Monotonic { i }`---commitments are append-only],
    [`nullifier_set_root: MerkleRoot`], [`Monotonic { i }`---spent nullifiers append-only],
    [`spend_authorization`], [`StateConstraint::Witnessed(WP { kind: Custom { vk_hash: blinded_spend_air_vk }, ... })`],
  ),
  caption: [`BlindedQueue` slot layout. The single new `WitnessedPredicateKind` (`Custom`) registers via the `WitnessedPredicateRegistry`---no new `Effect`, no new AIR row in the Effect VM proper.],
)

The spend AIR proves: (a) the commitment is in the queue's `commitment_set_root`, (b) the nullifier $nu = "Poseidon2"(C || k)$ is correctly derived, (c) the withdrawer knows $k$. Withdrawals are processed as standard Turns whose `Authorization::Custom { predicate, descriptor }` carries the spend proof; the executor's auth-mode dispatch (see §3) routes to the registered verifier.

=== RelayOperator

A `RelayOperator` is a cell that provides store-and-forward infrastructure. Its `CellProgram` declares:

- `RateLimitBySum { i, max_sum, dur }`---bounded relay throughput per epoch.
- `FieldLte { i, max_shard_count }`---bounded number of erasure shards hosted.
- `SenderAuthorized { set_root_index }`---only paying customers may use the relay.

Relay operations are standard Turns: `Effect::Enqueue` to deposit (sender pays the deposit), `Effect::Dequeue` on delivery (deposit refunded). The relay's economic model is `StateConstraint::SumEqualsAcross { input_fields: [deposit_in], output_fields: [refund_out, fee_out] }`---the relay's fee comes out as a conservation residual.

=== Summary

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    table.header([*Primitive*], [*New `WitnessedPredicateKind`s needed*]),
    [CapInbox], [none---`SenderAuthorized` + `MonotonicSequence` + `WriteOnce` + `FieldLte`],
    [ProgrammableQueue], [none---vocabulary already lifted to `StateConstraint`],
    [PubSubTopic], [none after the `Dfa` `WitnessedPredicate` kind lands],
    [BlindedQueue], [one (`Custom { vk_hash }` for the spend AIR)],
    [RelayOperator], [none---`RateLimitBySum` + `FieldLte` + `SenderAuthorized`],
  ),
  caption: [Storage primitives and the predicate-kinds they require. Most need *zero* new kinds.],
)

== Space Banks

A _space bank_ is a governance-managed allocation of storage capacity within a federation. Each federation maintains a total storage budget $B_"total"$ (governance-configurable). Space banks partition this budget among cells:

$ B_"total" = sum_(i=1)^n "space_bank"(i)."allocation" $

Cells draw from their assigned space bank. When usage exceeds allocation, new storage requests enter a queue: the cell must either free existing storage (triggering GC) or request a governance vote to increase the bank.

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Operation*], [*Authorization*], [*Effect*]),
    [Allocate], [Governance vote], [Increase a cell's bank allocation],
    [Transfer], [Both cells consent], [Move allocation between banks],
    [Reclaim], [Governance vote], [Force-shrink an inactive cell's allocation],
    [Split], [Bank owner], [Divide allocation among sub-cells],
  ),
  caption: [Space bank operations. All require proof of authority.],
)

== Computron-Metered Storage

All persistent storage is metered in computrons with ongoing costs:

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, right, left),
    table.header([*Operation*], [*Cost*], [*Rationale*]),
    [Write (per byte, per epoch)], [1 computron], [Ongoing cost for persistent state],
    [Read (per byte)], [0.01 computrons], [Cheap reads encourage verification],
    [MerkleQueue enqueue], [$10 + |"msg"|$ computrons], [Inbox anti-spam],
    [Erasure shard storage], [0.5 computrons/byte/epoch], [Redundancy at half price],
    [Cell-program storage], [2 computrons/byte/epoch], [Programs are long-lived],
  ),
  caption: [Storage metering. Costs are governance-adjustable per federation.],
)

The key distinction from blockchain gas: storage costs are *ongoing* (per-epoch rent), not one-time.

== MerkleQueue Substrate

The `MerkleQueue` is the data-structure substrate underlying the cell-program patterns: a content-addressed append-only queue where each state has a unique root hash (BLAKE3 Merkle tree of entries). Each entry contains: content hash (BLAKE3 of the enqueued data), sender, deposit, enqueued height, size, TTL. The queue root is recomputed on every enqueue/dequeue:

$ "root"_n = "BLAKE3"("root"_(n-1) || "entry"_n."content_hash") $

In the cell-program view, the `MerkleQueue` is the *implementation* of certain `CellProgram` patterns; the cell's slots commit to the queue's root, and the cell's `StateConstraint`s enforce queue invariants.

=== Sender-Pays-Deposit Anti-Spam

The deposit formula prevents inbox flooding:

$ "deposit" = "base_fee" + |"msg"| times r_"byte" + "ttl" times r_"block" $

With defaults: $"base_fee" = 100$, $r_"byte" = 0.1$, $r_"block" = 1$. A 1 KiB message with 1000-block TTL costs $approx 1202$ computrons. The deposit is fully refunded when the recipient processes; on timeout, the deposit covers the storage cost.

== State Lifecycle and Deep Garbage Collection

Cell storage follows a lifecycle with automatic transitions:

#figure(
  table(
    columns: (auto, auto, auto, auto),
    align: (left, left, left, left),
    table.header([*Phase*], [*Condition*], [*Storage*], [*Behavior*]),
    [Birth], [Factory creation or genesis], [Full state], [Active participant],
    [Active], [Recent turn within TTL], [Commitment (sovereign) or full (hosted)], [Normal operation],
    [Decay], [No turn for $>$ TTL, storage rent unpaid], [Commitment only (frozen)], [Cannot execute turns; can pay rent to reactivate],
    [Forced Sovereignty], [Decay exceeds grace period], [Ejected from federation hosting], [Must self-host or lose state],
  ),
  caption: [Cell lifecycle phases. Decay is reversible (pay rent); forced sovereignty is permanent ejection from hosted state.],
)

=== Storage Rent

Hosted cells (federation stores full state) pay storage rent proportional to their state size:

$ "rent"_"epoch" = "state_size_bytes" times "rent_rate_per_byte" $

Sovereign cells (32-byte commitment only) pay a fixed minimal fee regardless of actual state size.

=== Epoch Rotation

Every $E_"rotation"$ epochs (governance-configurable, default 1000), the storage layer performs a rotation: enumerate insufficient-balance cells, transition to Decay, force-sovereignty after grace period, prune expired sovereign registrations, re-verify erasure shards, publish space-bank utilization metrics.

== Erasure Coding for Data Availability

Sovereign cells maintain their own state, but may opt into erasure-coded availability for their MerkleQueue inboxes. The state is encoded as $k$-of-$n$ Reed-Solomon shards distributed across federation nodes:

- *Data availability*: any $k$ shards reconstruct the full queue state. No single node holds enough to read the content alone.
- *Reduced per-node cost*: each node stores $1\/n$ of the data rather than a full copy.
- *Proof of storage*: nodes periodically prove they still hold their shard via random leaf queries against a committed shard Merkle root.
- *Half-price rate*: erasure-coded storage costs $0.5 times$ the standard rate.

== Why this matters

The "storage as cell programs" reframing is not a cosmetic refactor. Five things follow:

+ *One executor loop, not two.* The same `StateConstraint` evaluator runs for every state-modifying turn, regardless of whether the cell is implementing a queue, an inbox, a topic, a blinded set, or arbitrary app logic.
+ *Receipt-bound transitions.* Every storage mutation produces a `TurnReceipt`. The "Alice subscribed at epoch 47" event is now a verifiable receipt, not an operator-process commitment.
+ *Constructor transparency.* The `FactoryDescriptor` discloses the cell's invariants statically. Anyone can audit the slot caveats before instantiating.
+ *Userspace authoring.* Apps compose existing `Effect` variants and existing `StateConstraint`s. New apps need zero kernel changes.
+ *Soundness reduction.* Two implementations of the same algebra was twice the bug surface. One implementation, one audit, one upgrade path.
