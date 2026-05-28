# STORAGE-AS-CELL-PROGRAMS — every storage primitive is a cell-program pattern

**Date:** 2026-05-24. **Status:** design only. Read-only on code; one new
`.md`. **Companion docs:** `STORAGE-REFLECTIVITY-RBG-DFA-AUDIT.md`,
`PREDICATE-INVENTORY.md` (especially §9), `SLOT-CAVEATS-DESIGN.md`,
`SLOT-CAVEATS-EVALUATION.md`, `BOUNDARIES.md`, `CELL-CRATE-REVIEW.md`,
`STARBRIDGE-APPS-PLAN.md`, `DESIGN-max-custom-effects.md`,
`APPS-AS-USERSPACE-AUDIT.md`.

The settled thesis from those docs: **storage primitives are not new
Effects.** They are **cell-program patterns** — compositions of
existing `Effect` variants (`SetField`, `EmitEvent`, `Transfer`,
`Grant`/`Revoke`, `CreateCellFromFactory`) governed by `CellPrograms`
whose `StateConstraint`s are drawn from the post-Lane-G 21-variant slot
caveat vocabulary, plus, where genuinely needed, a
`WitnessedPredicate` for the witness-attached cases. The storage
crate's `CapInbox`, `ProgrammableQueue`, `PubSubTopic`, `BlindedQueue`,
and `RelayOperator` already supply the *data-structure* mechanics
(content-addressed Merkle queues, durable WAL, nullifier-set, fair
distribution). What they don't supply, and what the migration adds, is
*executor-mediated, turn-bound, AIR-shaped* enforcement: the queue's
invariants stop being operator-process Rust and start being
turn-evaluated `StateConstraint`s. The HTTP endpoints in
`app-framework/src/{inbox,queue,blinded}_endpoint.rs` collapse into
thin proxies that produce signed `Action` blobs; the executor is the
single enforcement loop.

This document is a recipe. For each storage primitive a future
implementation lane could pick up, the slot layout, the
`StateConstraints` set, the `FactoryDescriptor` shape, the app-side
`Effect` composition, the observability story (per `BOUNDARIES.md`),
the file/lines that become a thin re-export or get deleted, and the
risks are all named explicitly. A reader who wants to migrate
`CapInbox` should be able to skim §3.1 and have a build plan.

---

## §1. Thesis

### §1.1. Storage→Effect was the wrong abstraction

The audit (`STORAGE-REFLECTIVITY-RBG-DFA-AUDIT.md` Q1) showed that the
queue effects (`Effect::QueueAllocate / Enqueue / Dequeue / Resize /
AtomicTx / PipelineStep`) already land lossily: the on-chain queue is
four felts (`capacity`, `length`, `owner`, `program_vk_hash`) and the
storage crate's actual `MerkleQueue::root`, `DequeueProof`,
`QueueProgram` constraint set live one layer below the executor, in
operator-process memory, reachable only via the `app-framework` HTTP
shim. Five things go wrong from there:

1. **Authorization gap.** `app-framework`'s `POST /send` accepts
   client-asserted `sender_hex` (subscription CLAUDIT §P0-5). The
   storage primitive *has* `SenderAuthorized` as a `QueueConstraint`,
   but the executor never sees it — so the on-chain audit trail can
   never confirm "the action came from a member of the set."
2. **No receipt.** The queue's state transitions never produce a
   `TurnReceipt`. There's no `WitnessedReceipt` for "Alice
   subscribed at epoch 47." The append is a wire-level operator
   commitment that nobody outside the relay has a verifiable handle
   on.
3. **Two enforcement loops.** `storage::programmable::QueueConstraint`
   is a closed Rust enum evaluated by `evaluate_constraint` in
   `storage/src/programmable.rs:454-580`. `cell::program::StateConstraint`
   is a closed Rust enum evaluated by the executor at
   `turn/src/executor.rs:4020-4024`. The vocabularies overlap (`SenderAuthorized`,
   `RateLimit`, `MonotonicSequence`, `TemporalGate`, `PreimageGate`,
   `MinDeposit`, `MaxSize`); they evolved separately; they don't share
   AIR shape. Two implementations of the same algebra means twice the
   bugs.
4. **Adding a primitive means adding an Effect.** The naive path to
   "I want a topic" is `Effect::TopicCreate`, `Effect::TopicPublish`,
   `Effect::TopicSubscribe`. Then `Effect::BountyPost`,
   `Effect::BountyClaim` for bounties. Each new app proposes new
   effects; each new effect needs an AIR row, a cost-table entry, a
   cclerk wrapper, an executor branch. The effect surface bloats; the
   AIR's column count climbs; the constitution that names effects
   gets harder to govern.
5. **The constraint vocabulary is the right shape; the home is
   wrong.** The Lane G `SLOT-CAVEATS-DESIGN.md` already established
   that `QueueConstraint`'s variants belong in `cell::program::StateConstraint`
   (Phase 1 alias is in `storage/src/programmable.rs:30-36`). The
   inversion that completes the lift: stop having the storage crate
   apply its own constraint vocabulary to its own data structures.
   Instead, have *cells* declare those constraints, and let the
   executor enforce them as part of the same per-turn evaluator that
   already runs.

### §1.2. Storage→cell-program-pattern is the right one

`PREDICATE-INVENTORY.md §9` makes the strong claim concrete: every
storage primitive's predicate needs are met by the unified inventory.

| Primitive | New predicate kinds needed |
|---|---|
| CapInbox | none — `SenderAuthorized` + `MonotonicSequence` + `WriteOnce` + `FieldLte` |
| ProgrammableQueue | none — vocabulary already lifted to `StateConstraint` |
| PubSubTopic | none after the DFA `WitnessedPredicate` kind lands |
| BlindedQueue | one (`WitnessedPredicate::Custom { vk_hash }` for the spend AIR) |
| RelayOperator | none — `RateLimitBySum` + `FieldLte` + `SenderAuthorized` |

This is the unification claim, viewed from the storage side: there is
no per-primitive enforcement loop. The same evaluator the executor
runs for every state-modifying turn enforces queue invariants,
inbox sequencing, blinded-spend correctness, relay quota. New
storage primitives plug in by *declaring a new composition of existing
predicates* (or, in the BlindedQueue case, registering one new
`vk_hash`-keyed `WitnessedPredicate` verifier). No new Effects, no
new AIR row, no new cclerk wrapper.

The migration that follows from this:

- Each storage primitive becomes a **factory** (`FactoryDescriptor`)
  that declares the slot layout + `state_constraints` field
  (`cell/src/factory.rs:180-192` already supports this).
- App code uses the **existing** `createFromFactory` extension-cclerk
  method (`extension/src/page.ts` — `STARBRIDGE-APPS-PLAN.md §1.3`)
  to instantiate the cell.
- App code uses the **existing** `Effect::SetField`, `Effect::EmitEvent`,
  `Effect::Transfer`, `Effect::GrantCapability` to operate on the
  instance.
- The executor enforces the cell-program's `StateConstraint`s on each
  turn.
- Receipts commit the cell's state transition with a
  `WitnessedReceipt` whose scope follows from `BOUNDARIES.md`
  (federation cleartext-inside; sovereign cells acceptance-inside;
  observers commitment-inside).

This is *constructor transparency* per `cell::factory`: anyone with
the `factory_vk` can read the descriptor and know exactly what
invariants the cell will carry over its lifetime. It is *bearer
capability* per `cell::capability`: holders of a slot's cap can
exercise the cell. It is *receipt-bound transition* per
`turn::executor`: every modification produces a verifiable record.
None of those mechanisms are new; the migration is recognizing that
they were always sufficient.

---

## §2. The migration framework

Every storage primitive's migration follows the same six-step pattern.
This section names the pattern; §3 fills it in per primitive.

**Step 1. Define a `FactoryDescriptor` (cell-program VK + state
constraints declaring the schema).**

`FactoryDescriptor` (`cell/src/factory.rs:163-197`) carries:
- `factory_vk`: the factory's identity (BLAKE3 of the descriptor).
- `child_program_vk` / `child_vk_strategy`: the program every child
  cell will run.
- `state_constraints: Vec<StateConstraint>`: the perpetual slot
  caveats baked into the child's `CellProgram`. Per
  `cell/src/factory.rs:180-192`: *"these are the `StateConstraint`
  set installed on every cell produced by this factory. They are
  evaluated by the executor on every state-modifying turn (not just
  creation), giving lifetime invariants like `WriteOnce`,
  `Monotonic`, `FieldDelta`, etc."*
- `field_constraints: Vec<FieldConstraint>`: creation-time only
  (initial values).
- `allowed_cap_templates: Vec<CapTemplate>`: which capability grants
  the factory may make at creation time.
- `default_mode: CellMode`: `Hosted` (federation-evaluated) or
  `Sovereign` (agent-witnessed).
- `creation_budget: Option<u64>`: per-epoch cell-mint cap.

The descriptor is content-addressed and inspectable. A starbridge-app
asking the cclerk to `createFromFactory(inbox_factory_vk, ...)` is
asking for "make me a cell that satisfies *this published contract*."

**Step 2. Author the cell-program (slot layout + state constraints +
WitnessedPredicates as needed).**

The author publishes:
- A documented **slot layout** (which `StateConstraint`s key into
  which slot index).
- A `Vec<StateConstraint>` from the 21-variant vocabulary in
  `SLOT-CAVEATS-DESIGN.md §1` (lifted into `cell::program`).
- Where needed (BlindedQueue, for example), one or more
  `WitnessedPredicate::Custom { vk_hash }` registrations against the
  registry in `cell::predicate` (per `PREDICATE-INVENTORY.md §3.3`).

The author's deliverables fit in roughly 200 LOC per primitive:
slot-index constants, a `pub fn descriptor() -> FactoryDescriptor`,
and unit tests for adversarial state transitions.

**Step 3. App creates instances via `Effect::CreateCellFromFactory`.**

This effect already exists (`turn/src/action.rs:625-634`), is wired
into the executor (`turn/src/executor.rs:7100-7125`), has full AIR
support (`circuit/src/effect_vm.rs:864-880`), and is exposed via the
extension cipherclerk's `createFromFactory` method
(`extension/src/page.ts`, `STARBRIDGE-APPS-PLAN.md §1.3`). The app
code is:

```ts
const inboxCellId = await window.dregg.createFromFactory(
    INBOX_FACTORY_VK,
    ownerPubkeyHex,
    /* initial_fields */ { 0: minDeposit, 1: capacity, 7: senderSetRoot }
);
```

No new cclerk API. No new effect.

**Step 4. App operates on the instance via existing Effects.**

The operations are *compositions of existing effects under a turn*:

```rust
// CapInbox send (replaces POST /inbox/send)
let action = app_cclerk.make_action(
    inbox_cell,
    "send",
    vec![
        Effect::SetField {
            cell: inbox_cell,
            slot: SEQ_SLOT,
            value: next_seq,
        },
        Effect::SetField {
            cell: inbox_cell,
            slot: MSG_SLOT_BASE + next_seq,
            value: payload_commitment,
        },
        Effect::EmitEvent {
            cell: inbox_cell,
            kind: "inbox.sent",
            data: payload_commitment_blob,
        },
    ],
);
```

The action carries the sender's signature (or proof). The executor
evaluates the cell's `CellProgram` over `(old_state, new_state, ctx)`;
the constraints reject the action if the sender isn't authorized or
the sequence number isn't `old + 1` or the slot at
`MSG_SLOT_BASE + next_seq` was already written.

**Step 5. Constraints enforce invariants at executor-eval time.**

The executor's existing `Cell::program.evaluate(new_state, old_state,
&eval_ctx)` call (`SLOT-CAVEATS-DESIGN.md §2`) is the single point of
enforcement. `MonotonicSequence` rejects a replay; `WriteOnce` rejects
overwriting a slot; `SenderAuthorized` rejects an outsider; `FieldLte`
rejects exceeding capacity. No storage-side enforcement loop; no
duplicate evaluator.

**Step 6. Receipt commits the new cell state; observers verify.**

The turn produces a `TurnReceipt` (and, for sovereign cells, a
`WitnessedReceipt`) binding `(old_commit, new_commit, effects_hash)`.
Observers consume per `BOUNDARIES.md §5.1`:

- **Cleartext-inside** the federation that hosts the cell (federation
  sees full state).
- **Commitment-inside** anyone holding the cell's
  `public_field_view` (sees committed slots).
- **Acceptance-inside** STARK verifiers of any witnessed predicate
  attached.
- **Out-of-band** everyone else.

The point is that **observers see what the boundary contract says
they see, derived from the algebra of the cell program**, not from
the conventions of an operator-side HTTP server.

---

## §3. Per-primitive reference designs

Each subsection follows the same template: slot layout, declared
constraints, `FactoryDescriptor` sketch, app-side operations,
observability, what it replaces, migration risk.

### §3.1. `CapInbox` — monotonic-sequenced WriteOnce slots

Source today: `storage/src/inbox.rs` (588 LOC). The "store-and-forward
subscriber delivery" primitive used by `apps/subscription`
(`apps/subscription/src/delivery.rs:138`). Per the CLAUDIT, the
only "real `dregg` primitive use" in the subscription app — and
also the surface where the authorization gap (§1) bites hardest.

#### Slot layout

A CapInbox cell holds:

| Slot | Name | Type | Purpose |
|---:|---|---|---|
| 0 | `head_seq` | FieldElement (u64) | Next sequence number the producer will write. Strictly increasing per send. Read by consumer as bookmark. |
| 1 | `tail_seq` | FieldElement (u64) | Next sequence number the consumer will read. Strictly increasing per dequeue. Always `tail_seq <= head_seq`. |
| 2 | `capacity` | FieldElement (u64) | Maximum number of in-flight messages (`head_seq - tail_seq <= capacity`). Immutable. |
| 3 | `min_deposit` | FieldElement (u64) | Minimum anti-spam deposit a sender must pay. Immutable. |
| 4 | `owner_pk_hash` | 32-byte hash | Hash of the inbox owner's pubkey. Immutable; only the owner may dequeue. |
| 5 | `sender_set_root` | 32-byte Merkle root | Poseidon2 root of authorized senders. Monotonic (insertions only). |
| 6 | `total_deposits_held` | FieldElement (u64) | Conservation slot: tracks sum of deposits. Decreases only on dequeue+refund. |
| 7 | `message_root` | 32-byte commitment | Poseidon2 root over the inbox's message ring. Updated on send and dequeue. |

Slots 0-3 are the queue metadata; slot 4 binds the owner; slot 5
holds the authorized-sender set; slot 6 is conservation
bookkeeping; slot 7 is the ring root.

The message bodies themselves are *not in slots*. They live in an
out-of-band commitment ring whose root is slot 7. The producer
publishes `(seq, payload_commitment)` pairs; the consumer dequeues
by presenting a Merkle proof of inclusion against slot 7's root. This
matches `MerkleQueue::root` from `storage::queue`.

#### StateConstraints declared

```rust
vec![
    // ─── identity / immutables ───
    StateConstraint::Immutable { index: 2 },  // capacity
    StateConstraint::Immutable { index: 3 },  // min_deposit
    StateConstraint::Immutable { index: 4 },  // owner_pk_hash

    // ─── sequencing ───
    StateConstraint::MonotonicSequence { seq_index: 0 },  // head_seq += 1 per send
    StateConstraint::MonotonicSequence { seq_index: 1 },  // tail_seq += 1 per dequeue
    // tail can never exceed head
    StateConstraint::FieldLte { index: 1, value: /* slot 0 */ ... },

    // ─── capacity bound ───
    // head_seq - tail_seq <= capacity. Encoded as a BoundedBy variant:
    // "head may only advance if (head - tail) < capacity".
    // In the v1 vocabulary this is the AnyOf form:
    //   AnyOf { variants: [(head unchanged), (head increased AND head-tail <= capacity)] }
    // Open question §7.2 (whether v1 supports relational lte across slots).

    // ─── sender authorization ───
    StateConstraint::SenderAuthorized {
        set: AuthorizedSet::PublicRoot { slot: 5 },
    },

    // ─── conservation ───
    StateConstraint::Monotonic { index: 6 },  // total_deposits never goes negative

    // ─── ring root must be touched on every send ───
    // Encoded as a transition predicate: if head_seq advanced, message_root must
    // also change; if head unchanged, ring root unchanged.
    // In v1: AllowedTransitions over (head_advanced, message_root_advanced) pairs.
    StateConstraint::AllowedTransitions {
        index: 7,
        transitions: vec![/* see §6.4 */],
    },
]
```

The expressive limit here is the "head - tail <= capacity" check
across two slots, which is **not** one of the 21 base variants per
`SLOT-CAVEATS-EVALUATION.md`. Per `SLOT-CAVEATS-EVALUATION.md §3.4`,
multi-slot relational checks are the cross-slot gap. Two options:

- **v1 (lazy):** encode as a DSL `Custom { constraint_hash,
  description: "inbox_capacity_bound" }`. Works today.
- **v2 (proper):** propose a new variant `FieldLteOther { index,
  other_index, plus_delta }` that says "new[index] <=
  new[other_index] + plus_delta". This is the cleanest expression of
  capacity bounds and would also serve auction phase-transition gating
  in `apps/gallery` (per `SLOT-CAVEATS-EVALUATION.md §2.6`).

The recommendation is **v1 (use `Custom` for the capacity-bound
check) for the migration commit, and propose `FieldLteOther` as a
follow-on**. The migration is not gated on the new variant.

#### FactoryDescriptor

```rust
pub fn inbox_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: INBOX_FACTORY_VK,
        child_program_vk: Some(INBOX_CHILD_PROGRAM_VK),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(INBOX_CHILD_PROGRAM_VK))),
        allowed_cap_templates: vec![
            CapTemplate {
                // Owner cap: holder can dequeue, advance tail.
                target: CapTarget::SelfCell,
                max_permissions: AuthRequired::Signature,
                attenuatable: true,
            },
            CapTemplate {
                // Sender cap: holder can send (advance head, write into ring).
                target: CapTarget::SelfCell,
                max_permissions: AuthRequired::Signature,
                attenuatable: true,
            },
        ],
        field_constraints: vec![
            // Initial state: head == tail == 0, ring root == EMPTY_RING.
            FieldConstraint::Equality { field_index: 0, value: 0 },
            FieldConstraint::Equality { field_index: 1, value: 0 },
            FieldConstraint::Range { field_index: 2, min: 1, max: 1_000_000 },
        ],
        state_constraints: /* as above */,
        default_mode: CellMode::Hosted,
        creation_budget: Some(10_000),  // per-epoch sybil resistance
    }
}
```

The descriptor is what the cipherclerk's `createFromFactory` consumes; the
constitution publishes the `INBOX_FACTORY_VK` so any starbridge-app
producing an inbox cell uses the same shape.

#### Operations as Effects

**Send (replaces `POST /inbox/send`):**

```rust
let payload_commitment = poseidon2(&payload);
let new_head = old_head + 1;
let new_ring_root = update_ring_root(old_ring_root, new_head, payload_commitment);

app_cclerk.make_action(
    inbox_cell,
    "send",
    vec![
        Effect::SetField { cell: inbox_cell, slot: 0, value: new_head },
        Effect::SetField { cell: inbox_cell, slot: 7, value: new_ring_root },
        Effect::SetField { cell: inbox_cell, slot: 6, value: old_total + deposit },
        Effect::Transfer { from: sender, to: inbox_cell, amount: deposit },
        Effect::EmitEvent {
            cell: inbox_cell,
            kind: "inbox.sent",
            data: postcard::to_allocvec(&(new_head, payload_commitment))?,
        },
    ],
)
```

The sender authenticates via signature; the executor checks
`SenderAuthorized` against slot 5; `MonotonicSequence` ensures
new_head == old_head + 1; `Custom` (or future `FieldLteOther`) checks
the capacity bound.

**Dequeue (replaces `GET /inbox/next`):**

```rust
let new_tail = old_tail + 1;
let new_ring_root = remove_from_ring(old_ring_root, new_tail);

app_cclerk.make_action(
    inbox_cell,
    "dequeue",
    vec![
        Effect::SetField { cell: inbox_cell, slot: 1, value: new_tail },
        Effect::SetField { cell: inbox_cell, slot: 7, value: new_ring_root },
        Effect::SetField { cell: inbox_cell, slot: 6, value: old_total - refund },
        Effect::Transfer { from: inbox_cell, to: sender_of_msg, amount: refund },
        Effect::EmitEvent {
            cell: inbox_cell,
            kind: "inbox.dequeued",
            data: postcard::to_allocvec(&(new_tail, dequeue_proof))?,
        },
    ],
)
```

The dequeuer authenticates as the inbox owner (owner-cap holder).

#### Observability (BOUNDARIES.md)

| Boundary | Population |
|---|---|
| **cleartext-inside** | The inbox-hosting federation (sees full state, slot values, every `EmitEvent` body). |
| **commitment-inside** | Anyone with `public_field_view` of the cell — sees committed `(head_seq, tail_seq, capacity, message_root)` but the per-message payload commitments only in aggregate. |
| **acceptance-inside** | Anyone verifying a STARK over the dequeue (membership proof against `message_root`) — learns that a message was dequeued at slot N without seeing the body. |
| **out-of-band** | Network observers without access to the cell's `public_field_view` or the events stream. |

Note: **the payload bodies themselves remain out-of-band** unless the
sender chooses to publish them in the event payload. The cell's
state slots commit only to the *ring root*, not to message bytes.
The producer-consumer pair can use end-to-end encryption layered on
top (as subscription already does with ChaCha20-Poly1305).

#### What it replaces

- `storage/src/inbox.rs` — most becomes thin re-exports:
  - `CapInbox::new` → cclerk `createFromFactory(INBOX_FACTORY_VK, ...)`.
  - `CapInbox::receive` / `receive_at` → `Effect::SetField(0, head+1) + Effect::SetField(7, new_root) + Effect::EmitEvent("inbox.sent")`.
  - `CapInbox::dequeue` / `read_next` → `Effect::SetField(1, tail+1) + Effect::SetField(7, new_root) + Effect::EmitEvent("inbox.dequeued")`.
  - `CapInbox::status` → `cell.state.public_field_view()` (slots 0, 1, 2).
- `app-framework/src/inbox_endpoint.rs` — entirely deletable; HTTP
  becomes a thin shim that translates `POST /send` into a signed
  `Action` blob and posts it to the executor.
- `apps/subscription/src/delivery.rs:138` — `receive_at` call becomes
  a cclerk `make_action` call. The framework gap noted in the
  comment ("CapInbox should grow a way to return the message body
  inline") is solved by the `EmitEvent` carrying the payload
  commitment, with the body fetched out-of-band by content hash
  (per the existing `delivery_log` pattern but now keyed on
  `EmitEvent` data).

Net LOC delta for the CapInbox migration: **~−400 in storage, ~+200
in cell-program + factory deployment, ~−300 in app-framework**. Net
~−500 LOC.

#### Migration risk

- **Capacity bound expressibility** (§3.1 above). Either use `Custom`
  in v1 (works, harder to audit) or land `FieldLteOther` first
  (cleaner, blocks the migration on a separate small change).
- **Message body delivery channel.** Today subscription stores
  ciphertext in `delivery_log` for re-fetch. The migration keeps
  this — the event carries the commitment, the body sits in a
  separate content-store. No semantic change.
- **Deposit refund timing.** `CapInbox::receive` charges the deposit;
  `dequeue` refunds. The migration encodes both as `Effect::Transfer`
  with conservation via slot 6. The risk is forgetting the refund on
  certain dequeue paths — the `Custom` constraint for
  `total_deposits_held == sum(in_flight_deposits)` is the safety net.
  Recommend explicit `SumEqualsAcross` between slot 6 and the
  per-message deposit ring.

### §3.2. `ProgrammableQueue` — already aliased, finish the collapse

Source today: `storage/src/programmable.rs` (1347 LOC). Per
`PREDICATE-INVENTORY.md §1.8`, the `QueueConstraint` vocabulary is
already (Phase 1) aliased to `cell::program::StateConstraint` (at
`storage/src/programmable.rs:30-36`). The migration is finishing
Option C from `SLOT-CAVEATS-DESIGN.md §5`: the
`ProgrammableQueue` *is* a cell whose program is
`CellProgram::Predicate(vec![StateConstraint::...])`.

This is the **proof-of-pattern primitive**: every variant in
`QueueConstraint` already has a `StateConstraint` counterpart, and
the storage-side evaluator and the cell-side evaluator should
collapse into the same function.

#### Slot layout

A programmable-queue cell's slots are the *generalized* CapInbox
layout, with the constraint set carrying additional invariants:

| Slot | Name | Type | Purpose |
|---:|---|---|---|
| 0 | `head_seq` | FieldElement (u64) | Producer cursor (per CapInbox). |
| 1 | `tail_seq` | FieldElement (u64) | Consumer cursor. |
| 2 | `capacity` | FieldElement (u64) | Max in-flight. |
| 3 | `program_vk` | 32-byte commitment | Hash of the cell-program's `state_constraints` — bound at creation. |
| 4 | `owner_pk_hash` | 32-byte hash | Owner identity. |
| 5 | `sender_set_root` | 32-byte commitment | Authorized senders (Merkle or BlindedSet). |
| 6 | `content_pattern_root` | 32-byte commitment | DFA route-table root for content-pattern constraints (slot is optional). |
| 7 | `ring_root` | 32-byte commitment | Message ring root. |

The shape is identical to CapInbox; the difference is the
`state_constraints` set the factory bakes into the cell-program,
which selects from a *richer menu*: any of the 21 lifted variants
plus, after `WitnessedPredicate` lands (`PREDICATE-INVENTORY.md §7`),
`StateConstraint::Witnessed(WP { kind: Dfa, commitment: slot[6] })`
for content-pattern classification.

#### StateConstraints declared

The set is *parameterized by the factory*. A canonical
"work-queue" descriptor:

```rust
vec![
    StateConstraint::MonotonicSequence { seq_index: 0 },
    StateConstraint::MonotonicSequence { seq_index: 1 },
    StateConstraint::Immutable { index: 2 },  // capacity
    StateConstraint::Immutable { index: 3 },  // program_vk
    StateConstraint::Immutable { index: 4 },  // owner
    StateConstraint::SenderAuthorized {
        set: AuthorizedSet::PublicRoot { slot: 5 },
    },
    StateConstraint::RateLimit {
        max_per_epoch: 10,
        epoch_duration: 100,
    },
    StateConstraint::TemporalGate {
        not_before: None,
        not_after: None,  // always-open by default
    },
    // After WitnessedPredicate Phase 3:
    StateConstraint::Witnessed(WitnessedPredicate {
        kind: WitnessedPredicateKind::Dfa,
        commitment: /* slot[6] */ ...,
        input_ref: InputRef::Witness { index: 0 },  // message body
        proof_witness_index: 1,
    }),
]
```

A "min-deposit auction-bid queue" descriptor swaps the constraint
set:

```rust
vec![
    // ... base sequencing ...
    StateConstraint::FieldGte { index: 8, value: MIN_DEPOSIT },  // bid ≥ floor
    StateConstraint::Monotonic { index: 8 },  // bids strictly non-decreasing
    StateConstraint::FieldGteHeight { index: 9, offset: 0 },  // valid_until ≥ now
]
```

Different factories produce different shapes; the executor enforces
each per the cell-program's static descriptor.

#### FactoryDescriptor

```rust
pub fn programmable_queue_factory(
    constraints: Vec<StateConstraint>,
    capacity: u64,
) -> FactoryDescriptor {
    let descriptor_hash = poseidon2(&postcard::to_allocvec(&constraints)?);
    FactoryDescriptor {
        factory_vk: PROGRAMMABLE_QUEUE_FACTORY_VK,
        child_program_vk: None,
        child_vk_strategy: Some(ChildVkStrategy::Derived {
            base_vk: PROGRAMMABLE_QUEUE_FACTORY_VK,
        }),
        // Each constraint set produces a derived child VK; provenance
        // records the param_hash so observers can reproduce the constraint.
        allowed_cap_templates: vec![/* owner, sender */],
        field_constraints: vec![
            FieldConstraint::Equality { field_index: 0, value: 0 },
            FieldConstraint::Equality { field_index: 1, value: 0 },
            FieldConstraint::Range { field_index: 2, min: 1, max: capacity },
            FieldConstraint::Equality { field_index: 3, value: u64_from_hash(descriptor_hash) },
        ],
        state_constraints: constraints,
        default_mode: CellMode::Hosted,
        creation_budget: Some(1_000),
    }
}
```

The `Derived` strategy means each constraint set produces a unique
child VK — anyone inspecting the queue cell can extract the
`param_hash` from `Provenance` and reproduce the constraint set
exactly. This is `ChildVkStrategy::Derived` working as designed
(`cell/src/factory.rs:25-31`).

#### Operations as Effects

Identical shape to CapInbox §3.1, but the constraint set varies. All
the variant-specific behavior (rate limiting, temporal gating,
content classification) is in the executor's evaluator; the app
code is unchanged.

#### Observability

- **cleartext-inside** the federation; **commitment-inside** anyone
  with `public_field_view`; **acceptance-inside** verifiers of any
  attached `WitnessedPredicate`'s STARK; **out-of-band** the rest.
- The `content_pattern_root` (slot 6) is **cleartext-inside the
  route-table author** (the DFA's patterns are inspectable from the
  table); **commitment-inside** anyone with only the root (sees the
  DFA's commitment hash, can verify a classification proof without
  the table). Per `PREDICATE-INVENTORY.md §5.1`.

#### What it replaces

- `storage/src/programmable.rs:60-580` — the `QueueConstraint`
  enum, `QueueProgram`, `ValidationContext`, `evaluate_constraint`
  all become *aliases or deletions*. The constraint vocabulary is
  already in `cell::program`; the evaluator becomes a thin wrapper
  that calls `CellProgram::evaluate(new, old, &eval_ctx)`.
- `storage/src/programmable.rs:282-330` (`QueueFactory`) —
  redundant; subsumed by `cell::factory::FactoryDescriptor`. Delete.
- `app-framework/src/queue_endpoint.rs` — same fate as
  inbox_endpoint.rs; a thin Action-producing shim.
- `apps/dao-treasury/src/governance.rs` — replace
  `QueueConstraint::Custom` with `StateConstraint::Custom` (already
  type-aliased).
- `apps/amm/src/twap_queue.rs`, `apps/stablecoin/src/liquidation_queue.rs`
  — these apps are being **dropped** per
  `STARBRIDGE-APPS-PLAN.md §2`. The migration deletes them, not
  ports them.

Net LOC delta: **~−800 in storage, ~+150 in cell-program descriptors**.

#### Migration risk

- **`Custom { expr: String }` translation.** The legacy
  `QueueConstraint::Custom` carries a raw expression string; the
  lifted `StateConstraint::Custom { constraint_hash, description }`
  expects a registered DSL hash. Open question §7.1 below.
- **`ContentPattern` migration.** Today's `ContentPattern { pattern }`
  is a Rust enum variant with raw bytes. After the DFA `WitnessedPredicate`
  kind lands, this becomes `Witnessed(WP { kind: Dfa, commitment:
  route_table_root })`. Migration order: this variant moves *after*
  the DFA lane (`DFA-RATIONALIZATION-DESIGN.md`) lands. Until then,
  `ContentPattern` stays in `QueueConstraint`'s legacy enum.
- **Validation context plumbing.** The executor's `EvalContext`
  (per `SLOT-CAVEATS-DESIGN.md §2`) already carries `sender,
  current_height, current_epoch, sender_epoch_count, revealed_preimage`.
  These map 1:1 to `storage::programmable::ValidationContext`. The
  per-cell-per-sender epoch counter for `RateLimit` is the only
  piece that needs new wiring (the executor needs a `(cell, sender,
  epoch) -> count` table). Phase 3 of `SLOT-CAVEATS-DESIGN.md §8`
  estimates ~60 LOC for this.

### §3.3. `PubSubTopic` — append-only log with subscriber cursors

Source today: `storage/src/pubsub.rs` (531 LOC). One publisher,
multi-subscriber cursors over a shared `MerkleQueue`. Per the audit
(Q4.2), this is the substrate for streaming caps (audit #11) and
the bulletin-board / yellow-pages model.

#### Slot layout

| Slot | Name | Type | Purpose |
|---:|---|---|---|
| 0 | `head_seq` | FieldElement (u64) | Publisher's seq counter (monotonic). |
| 1 | `subscriber_cursors_root` | 32-byte commitment | Merkle root over `(subscriber_pk, last_read_seq)` pairs. |
| 2 | `publisher_pk_hash` | 32-byte hash | Publisher identity (immutable). |
| 3 | `subscriber_set_root` | 32-byte commitment | Membership-gated topics: authorized subscribers (optional). |
| 4 | `topic_id_hash` | 32-byte hash | Stable topic identity (used by gossip DFA). Immutable. |
| 5 | `event_root` | 32-byte commitment | Merkle root over published events. |
| 6 | `topic_filter_root` | 32-byte commitment | DFA route-table root for topic-filtered routing (optional). |
| 7 | `dedup_root` | 32-byte commitment | Merkle root of message-content hashes for idempotent publish (per `storage::dedup`). |

#### StateConstraints declared

```rust
vec![
    StateConstraint::Immutable { index: 2 },  // publisher_pk_hash
    StateConstraint::Immutable { index: 4 },  // topic_id_hash
    StateConstraint::MonotonicSequence { seq_index: 0 },  // publisher seq
    StateConstraint::Monotonic { index: 5 },  // event_root only grows
    StateConstraint::Monotonic { index: 1 },  // subscriber cursors only advance
    // Only the publisher may write events
    StateConstraint::SenderAuthorized {
        set: AuthorizedSet::PublicRoot { slot: 2 },
    },
    // Optional: only authorized subscribers may advance their cursors
    // (When slot[3] is set, otherwise public)
    // Encoded as a Custom predicate composing slot 3 and the dispatched action.
    StateConstraint::Monotonic { index: 7 },  // dedup root grows monotonically
    // After WitnessedPredicate lands: topic-filter classification on subscribe
    // (the subscriber's gossip pattern must match the topic's filter root)
    // — typically lives in CapabilityCaveat::Witnessed, not StateConstraint
]
```

The asymmetry between publish (one writer, authorized via slot 2)
and subscribe (many readers, optionally authorized via slot 3) is
encoded by two different `SenderAuthorized` patterns acting on
different `EmitEvent` kinds. The executor differentiates by the
`Action`'s named handler.

#### FactoryDescriptor

```rust
pub fn pubsub_topic_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: PUBSUB_TOPIC_FACTORY_VK,
        child_program_vk: Some(PUBSUB_TOPIC_PROGRAM_VK),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(PUBSUB_TOPIC_PROGRAM_VK))),
        allowed_cap_templates: vec![
            CapTemplate {
                target: CapTarget::SelfCell,
                max_permissions: AuthRequired::Signature,  // publisher
                attenuatable: false,
            },
            CapTemplate {
                target: CapTarget::SelfCell,
                max_permissions: AuthRequired::Signature,  // subscriber
                attenuatable: true,
            },
        ],
        field_constraints: vec![
            FieldConstraint::Equality { field_index: 0, value: 0 },
            FieldConstraint::Equality { field_index: 1, value: 0 },
        ],
        state_constraints: /* as above */,
        default_mode: CellMode::Hosted,
        creation_budget: Some(1_000),
    }
}
```

#### Operations as Effects

**Publish:**

```rust
app_cclerk.make_action(
    topic_cell,
    "publish",
    vec![
        Effect::SetField { cell: topic_cell, slot: 0, value: new_head },
        Effect::SetField { cell: topic_cell, slot: 5, value: new_event_root },
        Effect::SetField { cell: topic_cell, slot: 7, value: new_dedup_root },
        Effect::EmitEvent {
            cell: topic_cell,
            kind: "topic.published",
            data: postcard::to_allocvec(&(new_head, payload_commitment))?,
        },
    ],
)
```

**Subscribe (advance cursor):**

```rust
app_cclerk.make_action(
    topic_cell,
    "subscribe",
    vec![
        // Update the subscriber's cursor: write into the cursors merkle.
        // (The subscribers_cursors_root is updated to reflect new (pk, new_cursor) entry.)
        Effect::SetField { cell: topic_cell, slot: 1, value: new_cursors_root },
        Effect::EmitEvent {
            cell: topic_cell,
            kind: "topic.subscribed",
            data: postcard::to_allocvec(&(subscriber_pk, cursor))?,
        },
    ],
)
```

Subscribers read events out-of-band by Merkle-proving inclusion
against the `event_root`. The cell's slot 5 commits to the root;
proofs against it are independent of the cell's executor.

#### Observability

- **cleartext-inside** the federation; **commitment-inside**
  anyone with topic_id_hash (knows the topic exists, can verify
  events against `event_root`); **acceptance-inside** verifiers of
  any topic-filter DFA classification proof; **out-of-band** the
  rest.
- The cursors root commits to subscriber identities; whether
  individual subscribers are visible depends on the cursor-set's
  encoding (a Merkle tree leaks per-membership; a Poseidon2 set
  commitment is `commitment-inside`-only).

#### What it replaces

- `storage/src/pubsub.rs` — most becomes thin re-exports or
  deletions. `PubSubTopic::publish` → `Effect::SetField` set.
  `PubSubTopic::subscribe` → `Effect::SetField(1, new_cursors_root)`.
  `PubSubTopic::read_for` → out-of-band Merkle proof against slot 5.
- `storage/src/dedup.rs` (171 LOC) — folds into slot 7's
  monotonic-growing Merkle root. The DeduplicationFilter struct's
  contains/insert pattern becomes a state-constraint check.
- `app-framework`'s pubsub endpoint (if any) — becomes a
  thin Action-producing shim.

Net LOC delta: **~−400 in storage, ~+150 in cell-program**.

#### Migration risk

- **Subscriber-cursor encoding.** Today's `BTreeMap<PublicKey,
  usize>` (in `PubSubTopic`) is fast in operator memory but
  awkward in a slot. The migration commits to a Merkle root over
  `(pk, cursor)` pairs (slot 1). Update is O(log N) per turn — fine
  for thousands of subscribers, slow for millions. Beyond ~10^6
  subscribers, the topic needs a sharded representation (separate
  cell per subset of subscribers) — a known limit but not blocking
  for v1.
- **Idempotent publish across cells.** Today `DeduplicationFilter`
  is per-topic in memory. In the migration, slot 7's root grows
  monotonically; double-publish at the same content-hash is rejected
  by membership check. The deduplication window is the lifetime of
  the topic (no expiry), which is fine for normal workloads but
  expensive for high-throughput streams. Open question §7.5.
- **Gossip integration.** The DFA topic-filter (slot 6) integrates
  with `intent::gossip` (`DFA-RATIONALIZATION-DESIGN.md §6.2`). The
  migration is *not* gated on that integration — the topic primitive
  works without DFA gossip. The DFA gossip integration consumes the
  topic-filter root once it lands.

### §3.4. `BlindedQueue` — the only primitive needing a new vk_hash

Source today: `storage/src/blinded.rs` (980 LOC). The
"commitments-in, nullifiers-out" private-consumption queue. Per
`PREDICATE-INVENTORY.md §9.4`, the **only** primitive in the storage
inventory that requires a new `WitnessedPredicate::Custom { vk_hash }`
registration.

#### Slot layout

| Slot | Name | Type | Purpose |
|---:|---|---|---|
| 0 | `commitments_root` | 32-byte commitment | Poseidon2 root over the queue's blinded item commitments. Monotonic. |
| 1 | `nullifier_root` | 32-byte commitment | Root over spent-item nullifiers. Monotonic. |
| 2 | `capacity` | FieldElement (u64) | Max in-flight items. Immutable. |
| 3 | `consumer_pk_hash` | 32-byte hash | Consumer identity (immutable). |
| 4 | `commitment_count` | FieldElement (u64) | Number of items added (monotonic). |
| 5 | `nullifier_count` | FieldElement (u64) | Number of items spent (monotonic). |
| 6 | `spend_air_vk_commitment` | 32-byte hash | VK of the registered spend AIR (immutable; bound at creation). |
| 7 | `queue_id_hash` | 32-byte hash | Stable identity (immutable). |

The commitments and nullifiers themselves do not live in slots —
they live in the per-queue Merkle trees whose roots are slots 0 and
1. Operations write the *new root* into the slot after adding or
spending.

#### StateConstraints declared

```rust
vec![
    StateConstraint::Immutable { index: 2 },  // capacity
    StateConstraint::Immutable { index: 3 },  // consumer
    StateConstraint::Immutable { index: 6 },  // spend_air_vk
    StateConstraint::Immutable { index: 7 },  // queue_id_hash

    StateConstraint::Monotonic { index: 0 },  // commitments only added
    StateConstraint::Monotonic { index: 1 },  // nullifiers only added
    StateConstraint::Monotonic { index: 4 },  // count_added
    StateConstraint::Monotonic { index: 5 },  // count_spent
    // Spent count never exceeds added count
    StateConstraint::FieldLte { index: 5, value: /* slot 4 */ ... },
    // (Same cross-slot expressibility caveat as CapInbox.)

    // ─── the witnessed predicate ───
    StateConstraint::Witnessed(WitnessedPredicate {
        kind: WitnessedPredicateKind::Custom {
            vk_hash: BLINDED_QUEUE_SPEND_AIR_VK,
        },
        commitment: /* slot[6] = spend_air_vk_commitment */ ...,
        input_ref: InputRef::Witness { index: 0 },  // nullifier
        proof_witness_index: 1,  // STARK proof bytes
    }),
]
```

The `Witnessed` variant carries the bound predicate; the verifier
(registered against `BLINDED_QUEUE_SPEND_AIR_VK`) checks that the
consumer presented a valid spend proof: that the nullifier was
correctly derived from an item in the commitments tree (slot 0) and
hasn't been spent before (membership in slot 1's nullifier set).

#### FactoryDescriptor

```rust
pub fn blinded_queue_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: BLINDED_QUEUE_FACTORY_VK,
        child_program_vk: Some(BLINDED_QUEUE_PROGRAM_VK),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(BLINDED_QUEUE_PROGRAM_VK))),
        allowed_cap_templates: vec![
            CapTemplate {
                target: CapTarget::SelfCell,
                max_permissions: AuthRequired::Signature,  // producer
                attenuatable: true,
            },
            CapTemplate {
                target: CapTarget::SelfCell,
                max_permissions: AuthRequired::Proof,  // consumer (needs STARK)
                attenuatable: false,
            },
        ],
        field_constraints: vec![
            FieldConstraint::Range { field_index: 2, min: 1, max: 1_000_000 },
            FieldConstraint::Equality { field_index: 6, value: u64_from_hash(BLINDED_QUEUE_SPEND_AIR_VK) },
        ],
        state_constraints: /* as above */,
        default_mode: CellMode::Sovereign,  // private-consumption naturally sovereign
        creation_budget: Some(500),
    }
}
```

The `Sovereign` mode is the right default — the consumer is the
witness-holder and the federation only sees commitments and
acceptance.

#### Operations as Effects

**Add (producer enqueues a blinded item):**

```rust
let item_commitment = poseidon2(&item, &randomness);
let new_root = update_commitments_root(old_commitments_root, item_commitment);

app_cclerk.make_action(
    queue_cell,
    "add",
    vec![
        Effect::SetField { cell: queue_cell, slot: 0, value: new_root },
        Effect::SetField { cell: queue_cell, slot: 4, value: count_added + 1 },
        Effect::EmitEvent {
            cell: queue_cell,
            kind: "blinded.added",
            data: postcard::to_allocvec(&item_commitment)?,
        },
    ],
)
```

The commitment is published; the item itself is `out-of-band` to all
but the producer-consumer pair (typically encrypted to the consumer
via a sealed box).

**Consume (consumer spends an item, presenting a STARK proof):**

```rust
let nullifier = derive_nullifier(item, consumer_sk);
let spend_proof = prove_spend(&item, &randomness, &consumer_sk, &commitments_root)?;
let new_nullifier_root = update_nullifier_root(old_nullifier_root, nullifier);

app_cclerk.make_action(
    queue_cell,
    "consume",
    vec![
        Effect::SetField { cell: queue_cell, slot: 1, value: new_nullifier_root },
        Effect::SetField { cell: queue_cell, slot: 5, value: count_spent + 1 },
        Effect::EmitEvent {
            cell: queue_cell,
            kind: "blinded.consumed",
            data: postcard::to_allocvec(&nullifier)?,
        },
    ],
)
.with_witness(WITNESS_INDEX_NULLIFIER, &nullifier.to_bytes())
.with_witness(WITNESS_INDEX_PROOF, &spend_proof)
```

The executor evaluates the `Witnessed` constraint: it loads the
registered `BLINDED_QUEUE_SPEND_AIR_VK` verifier, feeds it
`(commitments_root, nullifier, proof_bytes)`, and accepts the action
iff the verifier returns `Ok`. The audit's recommendation
(`STORAGE-REFLECTIVITY-RBG-DFA-AUDIT.md` Q4.2 row 4) — extend
`Consumed { nullifier }` with `payload` — is handled here by the
`EmitEvent` data, which can carry any out-of-band-encrypted payload
the consumer wants to publish.

#### The vk-hash registry entry

Per `PREDICATE-INVENTORY.md §6.2` (recommendation: closed enum with
`Custom { vk_hash }` escape), the blinded-queue spend AIR registers
itself at startup:

```rust
// In storage/src/blinded.rs (or its successor):
pub const BLINDED_QUEUE_SPEND_AIR_VK: [u8; 32] = [...];  // BLAKE3 of the AIR's selector layout

pub struct BlindedQueueSpendVerifier;

impl WitnessedPredicateVerifier for BlindedQueueSpendVerifier {
    fn verify(
        &self,
        commitment: &[u8; 32],     // commitments_root from slot 0
        input: &PredicateInput<'_>, // nullifier from witness slot 0
        proof_bytes: &[u8],         // STARK proof from witness slot 1
    ) -> Result<(), WitnessedPredicateError> {
        // Reuses the existing NoteSpendingAir (storage/src/blinded.rs
        // already does this — "reuses NoteSpendingAir against the
        // queue's commitment tree instead of the note tree" per
        // STORAGE-REFLECTIVITY-RBG-DFA-AUDIT Q1.1).
        verify_blinded_queue_spend_air(commitment, input.as_bytes(), proof_bytes)
    }
    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::Custom { vk_hash: BLINDED_QUEUE_SPEND_AIR_VK }
    }
    fn name(&self) -> &'static str { "blinded_queue_spend" }
}

// Registered at WitnessedPredicateRegistry initialization:
registry.register_custom(BLINDED_QUEUE_SPEND_AIR_VK, Arc::new(BlindedQueueSpendVerifier));
```

This is **one new `vk_hash`-keyed verifier**. The infrastructure to
host it (`WitnessedPredicateRegistry`) is the §3 design in
`PREDICATE-INVENTORY.md` (Phase 1 of `§7.1`, ~250 LOC). The AIR
itself (`NoteSpendingAir` adapted for the blinded queue) already
exists. The migration's net new circuit-work is ~zero.

#### Observability

- **cleartext-inside** the producer-consumer pair (knows item,
  randomness, nullifier).
- **commitment-inside** anyone with the `commitments_root` (knows
  an item exists at index N, not its content).
- **acceptance-inside** the STARK verifier (the federation, on a
  hosted queue; only the consumer's host, on a sovereign queue).
  Learns that *some* item was spent without seeing which.
- **out-of-band** anyone without the cell's state.

Per `BOUNDARIES.md §2.10` and `PREDICATE-INVENTORY.md §5.5`.

#### What it replaces

- `storage/src/blinded.rs` — partial collapse. The
  `BlindedQueue::add` / `consume_private` paths become
  `Effect::SetField` + `Witnessed` constraint. The `Consumed` enum
  with optional payload becomes the event's data field. The
  `NoteSpendingAir` re-use stays as the registered verifier.
- `app-framework`'s `blinded_endpoint.rs` — thin Action-producing
  shim.

Net LOC delta: **~−400 in storage, ~+200 in cell-program +
verifier registration**.

#### Migration risk

- **VK governance.** Who can register a new `vk_hash` in the
  registry? Open question §7.1.
- **Sovereign vs hosted default.** Hosted blinded queue means the
  federation sees acceptance only — but it also means the federation
  participates in the cell's host. Sovereign means the consumer's
  agent is the prover; the federation never sees the proof, only
  the receipt. The `default_mode: CellMode::Sovereign` choice
  follows the privacy principle but is harder to debug in early
  starbridge-apps. Suggest **hosted as the v1 default**, with
  starbridge-apps opting into sovereign once observability tooling
  catches up.
- **Multi-spend-attempt detection.** Slot 1 (nullifier_root) being
  monotonic prevents *the same* nullifier from being added twice —
  the constraint check fails. But a malicious actor proving against
  a *stale* `commitments_root` (slot 0) could try to consume an
  item that was already added but using an old snapshot. The
  per-receipt commitment-snapshotting rule
  (`PREDICATE-INVENTORY.md §6.3`) handles this: the proof must
  reference the *current* root, and the verifier enforces the
  binding.

### §3.5. `RelayOperator` — DFA-dispatched store-and-forward

Source today: `storage/src/operator.rs` (738 LOC) + `storage/src/relay.rs`
(365 LOC). The bonded relay operator hosting `CapInbox`es on behalf
of others, with TTL-based pricing and dispute-resolution slashing.

This primitive crosses two design lanes: the cell-program migration
(this doc) and the DFA dispatch lane (`DFA-RATIONALIZATION-DESIGN.md`).
The cell-program shape is below; the DFA dispatch ties to the
`WitnessedPredicate { kind: Dfa }` caveat once that lands.

#### Slot layout

| Slot | Name | Type | Purpose |
|---:|---|---|---|
| 0 | `bond_amount` | FieldElement (u64) | Computrons posted as relay bond. Decreases only on slash. |
| 1 | `bond_min` | FieldElement (u64) | Minimum bond. Immutable. |
| 2 | `quota_bytes_per_epoch` | FieldElement (u64) | Per-epoch byte limit. Immutable. |
| 3 | `bytes_relayed_this_epoch` | FieldElement (u64) | Current-epoch byte counter (resets each epoch). |
| 4 | `hosted_inbox_root` | 32-byte commitment | Merkle root over hosted inbox cell ids. |
| 5 | `operator_pk_hash` | 32-byte hash | Operator identity. Immutable. |
| 6 | `route_table_root` | 32-byte commitment | DFA route table for dispatch (binds inbox routes to handlers). |
| 7 | `dispute_count` | FieldElement (u64) | Monotonic dispute counter. Triggers tier-down at thresholds. |

#### StateConstraints declared

```rust
vec![
    StateConstraint::Immutable { index: 1 },  // bond_min
    StateConstraint::Immutable { index: 2 },  // quota
    StateConstraint::Immutable { index: 5 },  // operator pk

    // Bond can only decrease on slash (BoundedBy: bond may decrease only if dispute_count advanced)
    StateConstraint::BoundedBy { index: 0, witness_index: 7 },
    // Bond floor
    StateConstraint::FieldGte { index: 0, value: /* slot 1 */ ... },
    // Quota enforcement: per-epoch bytes ≤ quota
    StateConstraint::RateLimitBySum {
        index: 3,
        max_sum_per_epoch: /* slot 2 */ ...,
        epoch_duration: EPOCH_LEN,
    },
    StateConstraint::Monotonic { index: 4 },  // inbox set grows
    StateConstraint::Monotonic { index: 7 },  // disputes only increase

    // Sender authorization: only the operator may register hosted inboxes
    StateConstraint::SenderAuthorized {
        set: AuthorizedSet::PublicRoot { slot: 5 },
    },

    // After WitnessedPredicate Phase 3:
    // Relay dispatch must DFA-match the route table
    StateConstraint::Witnessed(WitnessedPredicate {
        kind: WitnessedPredicateKind::Dfa,
        commitment: /* slot[6] = route_table_root */ ...,
        input_ref: InputRef::Witness { index: 0 },  // incoming message bytes
        proof_witness_index: 1,
    }),
]
```

The DFA caveat is the "scope-this-relay-to-this-pattern" constraint:
the operator declares (via the route_table_root) which messages it's
willing to dispatch. A message that doesn't match the DFA is rejected
at constraint evaluation.

#### FactoryDescriptor

```rust
pub fn relay_operator_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: RELAY_OPERATOR_FACTORY_VK,
        child_program_vk: Some(RELAY_OPERATOR_PROGRAM_VK),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(RELAY_OPERATOR_PROGRAM_VK))),
        allowed_cap_templates: vec![
            CapTemplate {
                target: CapTarget::SelfCell,
                max_permissions: AuthRequired::Signature,  // operator
                attenuatable: false,
            },
        ],
        field_constraints: vec![
            FieldConstraint::Range { field_index: 1, min: 100, max: 1_000_000 },  // bond_min
            FieldConstraint::Range { field_index: 2, min: 1_000, max: 1_000_000_000 },  // quota
        ],
        state_constraints: /* as above */,
        default_mode: CellMode::Hosted,
        creation_budget: Some(100),  // small — bonded operators are rare
    }
}
```

#### Operations as Effects

**Register a hosted inbox** (operator's cclerk):

```rust
app_cclerk.make_action(
    relay_cell,
    "register_inbox",
    vec![
        Effect::SetField { cell: relay_cell, slot: 4, value: new_hosted_root },
        Effect::EmitEvent {
            cell: relay_cell,
            kind: "relay.inbox_registered",
            data: postcard::to_allocvec(&inbox_cell_id)?,
        },
    ],
)
```

**Relay a message** (sender's cclerk, with operator co-signature
or attenuated cap):

```rust
app_cclerk.make_action(
    relay_cell,
    "relay",
    vec![
        Effect::SetField {
            cell: relay_cell,
            slot: 3,
            value: bytes_relayed + msg.len() as u64,
        },
        // Then route to the destination inbox — this can be a sub-action
        // or a separate effect, depending on Effect::Forward design.
        Effect::EmitEvent {
            cell: relay_cell,
            kind: "relay.dispatched",
            data: postcard::to_allocvec(&(target_inbox, msg_commitment))?,
        },
    ],
)
.with_witness(WITNESS_INDEX_MSG, &msg)
.with_witness(WITNESS_INDEX_DFA_PROOF, &dfa_classification_proof)
```

**Slash on dispute:**

```rust
governance_cclerk.make_action(
    relay_cell,
    "slash",
    vec![
        Effect::SetField { cell: relay_cell, slot: 0, value: bond - slash_amount },
        Effect::SetField { cell: relay_cell, slot: 7, value: dispute_count + 1 },
        Effect::Transfer { from: relay_cell, to: GOVERNANCE_TREASURY, amount: slash_amount },
        Effect::EmitEvent {
            cell: relay_cell,
            kind: "relay.slashed",
            data: postcard::to_allocvec(&(slash_amount, reason))?,
        },
    ],
)
```

The `BoundedBy` constraint ensures bond decrease is gated on the
dispute counter advancing — a malicious operator can't drain its
own bond without recording a dispute.

#### Observability

- **cleartext-inside** federation; **commitment-inside** anyone with
  the relay's `public_field_view`; **acceptance-inside** verifiers of
  the DFA classification proof (sees that *a* message was routed
  correctly); **out-of-band** everyone else.
- The message bodies are routed via `EmitEvent` data, which is
  cleartext-inside the federation. For confidential relay, the
  message body is encrypted out-of-band; the relay sees only the
  ciphertext.

#### What it replaces

- `storage/src/operator.rs` (738 LOC) — most collapses. Bond
  management, slashing, quota, hosted-inbox bookkeeping all become
  `Effect::SetField` + state-constraint enforcement. The
  `DeliveryDispute` enum's outcomes (`Slash`, `Refund`) map to
  `Effect::Transfer` + `Effect::SetField`.
- `storage/src/relay.rs` (365 LOC) — the store-and-forward
  primitive becomes the relay-operator cell's "relay" action.
- `storage/src/metering.rs` (169 LOC) — slot 3's `RateLimitBySum`
  replaces the cost-table-driven metering. The cost table itself
  lives in the executor (`turn/src/executor.rs:7905-7910`).

Net LOC delta: **~−800 in storage, ~+250 in cell-program**.

#### Migration risk

- **Dispute resolution venue.** Today the dispute is resolved
  off-chain via `DeliveryDispute::DisputeOutcome`. After migration,
  disputes become governance turns against the relay cell. The
  governance machinery (per `apps/governed-namespace`) must be in
  place; until then, slashes are operator-authority-only (which is
  the current state anyway, so no regression).
- **Multi-cell dispatch.** A `relay` action that touches *both* the
  relay cell and the target inbox is a cross-cell turn. `dregg`
  already supports multi-cell turns (per `turn::Turn`'s effect
  vector). The constraint is that **all** affected cells'
  `CellPrograms` are evaluated. The relay cell's program must allow
  the dispatch effect; the target inbox cell's program must allow
  the cross-cell-sent message. The DFA caveat on the relay cell
  validates the routing decision; the inbox cell's
  `SenderAuthorized` validates that the *relay* is an authorized
  sender (or that the dispatch presents an attenuated cap from a
  legitimate sender).
- **Quota epoch rollover.** Slot 3 (`bytes_relayed_this_epoch`)
  needs to reset each epoch. The executor's `EvalContext`
  (`SLOT-CAVEATS-DESIGN.md §2`) has `current_epoch`; the
  `RateLimitBySum` variant resets internally per-epoch. This
  requires the executor to track per-cell epoch counters — a small
  extension to the existing per-cell metadata.

---

## §4. Out-of-scope (truly system-level)

Two storage primitives **should not** become cell programs. The
recommendation is to keep them as system-level concerns with
careful boundary contracts.

### §4.1. `StorageMount` (`storage/src/namespace_mount.rs`, 466 LOC)

A storage mount is a wire/transport-level binding: *route data
addressed to path P to backing storage S*. Per the audit
(Q1.1), `StorageMount` exists as `StorageMountKind::{Inbox, PubSub,
WorkQueue, Bulletin}` but the executor never sees it. The four
kinds are simply enum variants the operator inspects to decide
which storage primitive to delegate to.

**Why not a cell program:**

1. **It's a routing decision, not a state machine.** A mount has no
   per-turn state transitions; it has a *static configuration*
   declaring "path X resolves to storage backend Y". The natural
   home is the constitution-bound route table
   (`wire::dfa_router::GovernedRouter`), not a cell.

2. **Mounts predate cell programs.** A mount is *infrastructure*; it
   exists so that a CapTP sturdy ref or a URI can resolve to a
   backing storage at all. Putting it in a cell creates a chicken-
   and-egg: how does the wire layer find the mount cell?

3. **The cell programs that *consume* mounts already exist.** Each
   `StorageMountKind` variant maps to a cell-program pattern
   (`Inbox` → §3.1, `PubSub` → §3.3, `WorkQueue` → §3.2,
   `Bulletin` → §3.3 variant). The mount itself is just the
   *resolver*.

**Recommendation: (b) becomes a special wire-level Effect.**

Specifically: `Effect::MountStorage { path: String, kind:
StorageMountKind, target_cell: CellId }` — a turn-mediated way to
declare a mount, but the *effect of the mount* is on the route
table, not on a cell's state. The mount cell, if any, is
governance-bound (per `apps/governed-namespace`); the route table
swap is via `GovernedRouter`'s constitutional update path.

The implementation would lift `StorageMount::register` into a wire-
level effect, with the route table itself remaining the source of
truth. The constitution publishes the route-table-root commitment;
mount effects produce signed updates that anyone can verify.

Net change for namespace_mount.rs: stays as the route-table-update
machinery; loses the `StorageMountKind::{Inbox,...}` enum (those
become "the kind of cell program the target_cell runs", inspected
out-of-band by the resolver).

### §4.2. `ContentStore` (`storage/src/content.rs`, 188 LOC)

A content-addressed blob store: BLAKE3 → bytes. Per the audit
(Q4.2), this is the candidate for `Effect::BindBlob` (audit #15).

**Why not a cell program:**

1. **Data volumes are wrong for cell state.** A typical content-
   addressed blob is kilobytes to megabytes. A cell has 8 slots ×
   32 bytes = 256 bytes of state. Even with `BlobCommitment`
   sub-cells, the actual *bytes* belong in a separate storage tier
   (host filesystem, IPFS, Arweave, S3, depending on deployment).

2. **No transitions worth proving.** A blob is *immutable* — write
   once, then read-only forever. There's no state machine to
   constrain; once the BLAKE3 is bound to bytes, nothing changes.
   `WriteOnce` is the only constraint, and it doesn't justify a
   full cell program.

3. **The natural cell-program pattern is `Effect::BindBlob` on a
   commitment-holding cell.** A cell can hold the BLAKE3 hash of a
   blob in a slot (immutable, write-once); the bytes live in a
   ContentStore the federation manages. The audit's `Effect::BindBlob`
   is the right shape: a turn-mediated registration that the
   content-store SHOULD make available, with availability proven
   by reading the bytes back and verifying the hash.

**Recommendation: (a) stays in storage/ as operator-side, paired
with a new `Effect::BindBlob { cell, slot, hash, uri }` that
records the blob's *commitment* in a cell slot but stores the
*bytes* operator-side.**

The cell-side concern is the commitment (32-byte hash). The
content-store concern is the actual byte storage, retention, GC,
and availability. The two coordinate via the
`AttestedRoot`-bound availability protocol (relays attest that
they hold the bytes; clients verify by hash).

**Open question §7.3:** is content-addressed blob storage dregg's
responsibility at all, or does it belong to the host node (with
dregg committing only to hashes)? The recommendation leans toward
"host node responsibility; dregg commits to hashes" — which means
`storage::content` becomes a *host*-level concern, not a workspace
crate.

Net change for content.rs: stays as the operator-side BLAKE3 store.
Loses any direct linkage to cell state; gains an
`Effect::BindBlob`-aware adapter (likely in `app-framework` or a
new `node::content_adapter` module).

---

## §5. Apps that consume the migrations

This section walks each starbridge-app from `STARBRIDGE-APPS-PLAN.md
§2` and names which storage primitives it would use post-migration.

### §5.1. `apps/subscription/` (existing storage-layer case study)

Today uses `CapInbox::receive_at` (per `apps/subscription/src/delivery.rs:138`).

**Post-migration shape:**

- One `CapInbox` cell per subscriber, created via
  `createFromFactory(INBOX_FACTORY_VK, subscriber_pk, ...)`. The
  factory descriptor declares `MonotonicSequence` + `WriteOnce` +
  `SenderAuthorized { set: creator_set_root }` so only the
  subscribed creator may send to the subscriber's inbox.
- Creator's `deliver` operation becomes the `Effect::SetField` set
  from §3.1, signed by the creator. Authorization gap (subscription
  CLAUDIT §P0-5) closes: the executor enforces
  `SenderAuthorized` against the creator-set root.
- Subscriber's content-fetch is unchanged: still an out-of-band
  fetch keyed on the event's payload commitment.
- The epoch-keyed dedup that was an in-process `HashMap<(PublicKey,
  u64), u64>` becomes an `Effect::ClaimSlot { domain:
  subscription_id, key: epoch_hash }` (audit Tier-1 #5; out of scope
  for this doc but the integration point is the subscription
  factory's program).

**Storage primitives consumed:** `CapInbox` (§3.1).

**Code shape:**

```rust
// Creator delivers content to subscriber.
fn deliver_content(
    creator: &AgentCipherclerk,
    subscriber_inbox: CellId,
    content_ciphertext: &[u8],
    epoch: u64,
) -> Result<TurnReceipt> {
    let payload_commitment = poseidon2(content_ciphertext);
    let new_head = creator_local_state.head_seq + 1;
    let new_ring_root = update_ring_root(
        creator_local_state.message_root,
        new_head,
        payload_commitment,
    );
    let action = creator.make_action(
        subscriber_inbox,
        "deliver",
        vec![
            Effect::SetField { cell: subscriber_inbox, slot: 0, value: new_head },
            Effect::SetField { cell: subscriber_inbox, slot: 7, value: new_ring_root },
            Effect::EmitEvent {
                cell: subscriber_inbox,
                kind: "content.delivered",
                data: postcard::to_allocvec(&(new_head, payload_commitment, epoch))?,
            },
        ],
    );
    creator.submit_turn(action)
}
```

### §5.2. `governed-namespace`

Per `STARBRIDGE-APPS-PLAN.md §2`: DAO-governed routing table +
capability-secure file storage; propose/vote/amend routes.

**Storage primitives consumed:**
- `ProgrammableQueue` (§3.2) for the proposal queue. The constraint
  set: `SenderAuthorized` (voter roll), `MonotonicSequence` (proposal
  ids), `TemporalGate` (voting windows).
- `PubSubTopic` (§3.3) for amendment-notification streams (notify
  members of new proposals).
- `Effect::BindBlob` (§4.2) for the actual file content; the route
  table commits to the hash in cell slots.

### §5.3. `gallery` (auction)

**Storage primitives consumed:**
- `ProgrammableQueue` (§3.2) for the bid queue (constraint:
  `MonotonicSequence` on bid_seq, `FieldGte` on bid_amount slot).
- `PubSubTopic` (§3.3) for live-bid-feed subscription (audit Tier-3
  #11).
- `BlindedQueue` (§3.4) for the private-Vickrey variant (sealed bids
  → consumed by coordinator at reveal time).
- `Effect::BindBlob` (§4.2) for the artwork image content.

### §5.4. `bounty-board`

**Storage primitives consumed:**
- `ProgrammableQueue` (§3.2) for the claim queue (constraint:
  `SenderAuthorized` against the qualification proof attesters,
  `RateLimit` per-worker, `TemporalGate` for the bounty deadline).
- `BlindedQueue` (§3.4) for private claims (audit Tier-3 #12 — the
  payload return channel naturally fits the `EmitEvent` data slot).
- `PubSubTopic` (§3.3) for bounty announcements.

### §5.5. `nameservice`

**Storage primitives consumed:**
- `CapInbox` (§3.1) for the dispute evidence queue (one per name
  cell; only the disputant may send).
- `PubSubTopic` (§3.3) for rename-notification (the reverse-index
  cell subscribes to all per-name cells).
- `ProgrammableQueue` (§3.2) for the rent-payment queue (constraint:
  `MonotonicSequence` on payment seq, `FieldDelta` on the linked
  `expiry_height` slot).

### §5.6. `privacy-voting`

**Storage primitives consumed:**
- `BlindedQueue` (§3.4) for the commit queue — sealed ballot
  commitments. Spend (reveal) produces a nullifier proving the
  ballot was committed exactly once. **This is the canonical
  BlindedQueue use case post-migration.**
- `PubSubTopic` (§3.3) for tally publication.
- `Effect::ClaimSlot` (audit Tier-1 #5) for nullifier-based
  double-vote prevention; orthogonal to BlindedQueue.

### §5.7. `identity`

**Storage primitives consumed:**
- `CapInbox` (§3.1) for credential delivery to holders
  (encrypted; sender = issuer).
- `PubSubTopic` (§3.3) for credential schema announcements + global
  revocation notifications.

### §5.8. `compute-exchange`

**Storage primitives consumed:**
- `ProgrammableQueue` (§3.2) for the job queue (constraint:
  `SenderAuthorized` against authorized buyers, `TemporalPredicate`
  on seller standing — once the temporal predicate WitnessedKind
  lands).
- `RelayOperator` (§3.5) for the job-dispatch relay between
  buyer and seller cells.
- `BlindedQueue` (§3.4) for sealed-bid orders.
- `PubSubTopic` (§3.3) for live-market data.

**The fully-loaded starbridge-app:** uses all five migration
primitives. This is the "integration test that lights up every
Tier-1 primitive" (per `SLOT-CAVEATS-EVALUATION.md §2.8`).

---

## §6. Storage crate disposition

After all five primitive migrations land, the storage crate
becomes:

### §6.1. Thin re-exports

These files become thin re-exports of cell-program / factory machinery:

| File | LOC today | Post-migration | Net change |
|---|---:|---|---:|
| `storage/src/inbox.rs` | 588 | Re-export `INBOX_FACTORY_VK`, `inbox_factory_descriptor()`, helper builders. ~50 LOC. | −538 |
| `storage/src/programmable.rs` | 1347 | Re-export `programmable_queue_factory()`, constraint-set helpers. ~100 LOC. | −1247 |
| `storage/src/pubsub.rs` | 531 | Re-export `pubsub_topic_factory_descriptor()`. ~50 LOC. | −481 |
| `storage/src/blinded.rs` | 980 | Re-export factory + `BlindedQueueSpendVerifier`. ~150 LOC (keeps the AIR). | −830 |
| `storage/src/operator.rs` | 738 | Re-export `relay_operator_factory_descriptor()`. ~80 LOC. | −658 |
| `storage/src/relay.rs` | 365 | Folded into operator.rs. | −365 |
| `storage/src/dedup.rs` | 171 | Folded into pubsub state-constraint check. | −171 |
| `storage/src/atomic.rs` | 460 | Stays (Effect::QueueAtomicTx machinery is orthogonal). | 0 |
| `storage/src/dataflow.rs` | 673 | Stays (Pipeline orchestration is orthogonal). | 0 |

### §6.2. Outright deleted

| File | LOC today | Reason |
|---|---:|---|
| `storage/src/metering.rs` | 169 | Per-cell `RateLimitBySum` replaces; cost table moves to executor. |
| `storage/src/namespace_mount.rs` | 466 | Becomes a wire-level `Effect::MountStorage` (§4.1). |
| `storage/src/quota.rs` | 213 | Subsumed by the relay-operator cell's slot 3 (`RateLimitBySum`). |
| `storage/src/sharding.rs` | 347 | Cross-cell concern; folds into the cell layer. |

### §6.3. Stays (truly low-level)

| File | LOC today | Reason |
|---|---:|---|
| `storage/src/commitment.rs` | 890 | Typed dual-form commitments are infrastructure; many crates depend on them. |
| `storage/src/queue.rs` | 620 | `MerkleQueue` is the underlying data structure; cell programs commit to its root. |
| `storage/src/content.rs` | 188 | Operator-side blob store (§4.2). |
| `storage/src/erasure.rs` | 265 | Availability-sampling infrastructure. |
| `storage/src/multi_asset.rs` | 404 | Fee accounting; orthogonal. |
| `storage/src/wal.rs` | 536 | Durable backing for `MerkleQueue`. |
| `storage/src/poly_queue.rs` | 1456 | KZG-backed; feature-gated; orthogonal. |

### §6.4. Net LOC delta

| Category | Delta |
|---|---:|
| Thin re-exports (5 files) | −4290 |
| Outright deleted (4 files) | −1195 |
| New cell-program code (5 factories × ~250 LOC) | +1250 |
| New verifier registration (BlindedQueue) | +150 |
| App-framework HTTP shims (5 endpoints) | ~−1000 |
| **Net** | **~−5000** |

Roughly **5000 LOC removed from `dregg-storage` and `app-framework`**,
replaced by **~1400 LOC of cell-program declarations and factory
descriptors**, plus the (separately budgeted)
`WitnessedPredicateRegistry` infrastructure from
`PREDICATE-INVENTORY.md §7.1`.

---

## §7. Open questions for the designer

These are the calls the design surface implies but doesn't decide.
Each is tagged with the recommendation but the designer should
explicitly confirm.

### §7.1. BlindedQueue's vk-hash registry entry — who generates the VK?

The `WitnessedPredicateRegistry` (per `PREDICATE-INVENTORY.md §3.3`)
holds the verifier for `BLINDED_QUEUE_SPEND_AIR_VK`. The questions:

- **Who owns the STARK circuit definition?** The AIR lives in
  `storage/src/blinded.rs` today (the NoteSpendingAir re-use). After
  migration, it stays there — but the circuit's authority is the
  workspace, not an external library. Recommendation: **the
  workspace owns the VK; constitution publishes the
  vk_hash**.

- **What generates the vk?** The same Plonky3 prover that generates
  other workspace VKs. The vk_hash is the BLAKE3 of the AIR's
  selector layout (per `cell::factory::CapTemplate::hash` style).
  Recommendation: **a `build.rs` script in the cell-program crate
  computes and writes the vk_hash; it's a build-time constant**.

- **Who can register new vk_hashes?** The
  `WitnessedPredicateRegistry::register_custom` is callable from
  cell-program declarations. The risk is malicious registration —
  per `PREDICATE-INVENTORY.md §10.6` ("the Custom escape is a
  partial-trust surface"). Recommendation: **constitution-bound
  list of `(vk_hash, verifier_name)` pairs; deployment-time
  validation rejects unknown vk_hashes**. Same audit discipline as
  `Effect::Custom`.

### §7.2. Cross-slot relational constraints (`head - tail <= capacity`)

The CapInbox capacity bound and the BlindedQueue
"spent ≤ added" both need a *cross-slot* comparison. The 21-variant
vocabulary doesn't include this; the workarounds are `Custom` or a
new variant `FieldLteOther`.

Recommendation: **propose `FieldLteOther { index, other_index,
plus_delta }` as a Phase-1.5 variant**, landing between
`SLOT-CAVEATS-DESIGN.md` Phase 1 (the 21 lifted variants) and
Phase 4 (the first app migration). Approximate cost: 40 LOC + 6
tests. Without it, the storage migration relies on `Custom` for
these checks, which works but is harder to audit.

### §7.3. `StorageMount` disposition

**Recommendation (per §4.1): wire-level Effect, with the route
table as the source of truth**. The current
`storage::namespace_mount::StorageMount` becomes a constitution-bound
configuration; the per-kind enums (`Inbox`, `PubSub`, etc.)
disappear because the targeted cell's `Provenance` already names its
factory.

### §7.4. `ContentStore` disposition

**Recommendation (per §4.2): host-level concern; dregg commits
only to hashes**. The `storage::content::ContentStore` becomes a
*host*-level (not workspace-level) concern. `Effect::BindBlob`
records the commitment in cell state; the host node serves the
bytes; the federation attests to availability via the existing
relay protocols.

This implies a doc-level boundary: blob storage moves out of
`dregg-storage` and into the **node-operator's** infrastructure.
Apps that need blob storage talk to the host through a
`dregg-content-adapter` shim (probably in `node/` or a new crate).

### §7.5. Migration ordering — which primitive migrates first?

Two candidates contend:

- **`ProgrammableQueue` first**: its vocabulary already matches
  (Lane G Phase 1 alias is in place). The migration is "delete the
  storage-side evaluator; have the executor evaluate the cell
  program." Risk: the lowest, but the visible payoff is also lowest
  (no app uses `ProgrammableQueue` outside dropped apps and
  governance).
- **`CapInbox` first**: highest visible payoff (closes
  subscription's CLAUDIT §P0-5 authorization gap; lays the
  groundwork for nameservice's dispute queue). Slightly higher
  risk (capacity bound + ring root semantics).

**Recommendation: `ProgrammableQueue` first as the proof-of-pattern
commit; `CapInbox` second as the first user-visible migration**.
The ProgrammableQueue migration is the moment the executor's
evaluator and the storage-side evaluator collapse into one — that's
the architectural achievement. CapInbox is the moment subscription
becomes correct end-to-end.

### §7.6. Idempotent-publish window for PubSubTopic

PubSub's slot 7 (`dedup_root`) grows monotonically; double-publish
is rejected by membership check. The window is the *lifetime of
the topic*. For high-throughput topics this is expensive (the
dedup set grows unboundedly).

**Recommendation: a Phase-2 `Effect::ResetDedupRoot` action
gated by a `TemporalGate` on the topic's epoch boundary**. The
topic publisher can opt into per-epoch dedup. For most apps this
isn't needed; for compute-exchange's high-throughput market
data feed it likely is.

### §7.7. Sovereign vs hosted default mode

Each primitive's `FactoryDescriptor` declares a `default_mode`. The
choices in §3 above:

- CapInbox: `Hosted` (federation sees content)
- ProgrammableQueue: `Hosted` (variable; depends on constraint set)
- PubSubTopic: `Hosted` (publication is intrinsically broadcast)
- BlindedQueue: `Sovereign` (privacy is the point)
- RelayOperator: `Hosted` (the relay is a federation participant)

**Recommendation: keep these defaults; let apps override via the
factory's `default_mode`**. The starbridge-apps in §5 mostly want
the default; identity and privacy-voting want sovereign for some
queues.

### §7.8. Capacity-bound vs throughput in the migration

A cell-program-enforced queue is *slower* than an operator-side
queue: every send is a turn, with the executor's full
constraint-evaluation overhead. The migration trades latency for
verifiability. For high-throughput cases (compute-exchange market
data, gallery live-bid feeds), the answer is to use
`Effect::QueueAtomicTx` to batch multiple sends into one turn (the
infrastructure exists per `turn::action::Effect::QueueAtomicTx`).

**Recommendation: document the trade-off; don't optimize prematurely.**
Apps that need batching use the existing atomic-tx effect.

---

## §8. Migration sequencing

Concrete order of operations, with dependencies and LOC estimates.

| Phase | What lands | Depends on | LOC estimate | Risk |
|---|---|---|---:|---|
| **0** | Slot caveats v1 (the 21 lifted variants from `SLOT-CAVEATS-DESIGN.md` Phases 1-3) | — | +600 | low |
| **0.5** | `FieldLteOther` variant (Open Q §7.2) | Phase 0 | +40 | low |
| **1** | `WitnessedPredicate` module + registry (Phase 1 of `PREDICATE-INVENTORY.md §7.1`) | Phase 0 | +250 | low |
| **2** | **ProgrammableQueue migration** — proof of pattern | Phase 0, Phase 1 | net −600 | medium |
| **3** | **CapInbox migration** — first user-visible | Phase 2 | net −400 | medium |
| **4** | **PubSubTopic migration** — gossip substrate | Phase 3; DFA rationalization for topic filters (`DFA-RATIONALIZATION-DESIGN.md`) | net −350 | medium |
| **5** | **RelayOperator migration** — after DFA lane | Phase 4; DFA `WitnessedPredicate::Dfa` kind (Phase 3 of `PREDICATE-INVENTORY.md §7.3`) | net −600 | high |
| **6** | **BlindedQueue migration** — needs vk-hash registry | Phase 1; BlindedQueueSpendVerifier registered | net −500 | medium |
| **7** | `storage::namespace_mount` lift to wire effect (Open Q §7.3) | Phase 5 | net −300 | medium |
| **8** | `storage::content` lift to host concern (Open Q §7.4) | independent | net −150 | medium |
| **9** | `app-framework` endpoint shims become Action-producers | all above | net −1000 | low |

**Total net LOC delta: ~−4000** (consistent with §6.4).

**Total elapsed time** (rough): Phases 0-1 are sequential
prerequisites and total ~3 weeks. Each per-primitive migration
(Phases 2-6) is roughly 1-1.5 weeks. Phases 7-9 are deletion-heavy
cleanups, ~1 week each. **Total: ~3 months calendar** for one
focused implementation lane to complete the migration. Two parallel
lanes (one on the caveat infrastructure, one on per-primitive
migrations) compress this to ~6 weeks.

**Per-phase commit shape:** each phase is 1-3 commits, each with
its own test suite. The `ProgrammableQueue` proof-of-pattern (Phase
2) is the architectural milestone; the `CapInbox` migration (Phase
3) is the architectural payoff.

---

## §9. Connection to apps

Specifically: which starbridge-app's build is gated on which storage
migration?

| App (per `STARBRIDGE-APPS-PLAN.md §2`) | Gated on |
|---|---|
| `subscription` | **CapInbox migration (Phase 3)**. Today the app uses `CapInbox::receive_at` and inherits the authorization gap. Post-Phase-3, the subscription delivery becomes turn-mediated and the CLAUDIT §P0-5 closes. |
| `nameservice` | **ProgrammableQueue migration (Phase 2)** for the rent-payment queue. Optionally **CapInbox migration (Phase 3)** for the dispute evidence queue. The first build (the "demo version" per `STARBRIDGE-APPS-PLAN.md §3.1`) is unblocked at Phase 2. |
| `identity` | **CapInbox migration (Phase 3)** for credential delivery to holders. **PubSubTopic migration (Phase 4)** for credential-schema announcements. The "least gap-blocked app" — identity is unblocked at Phase 3. |
| `governed-namespace` | **ProgrammableQueue migration (Phase 2)** for the proposal queue. **PubSubTopic migration (Phase 4)** for amendment notifications. **`Effect::BindBlob` (Phase 8 or its successor)** for file content. |
| `bounty-board` | **ProgrammableQueue migration (Phase 2)** for the claim queue. **BlindedQueue migration (Phase 6)** for private claims. **PubSubTopic migration (Phase 4)** for announcements. The full-feature build is gated on Phase 6. |
| `gallery` | **ProgrammableQueue migration (Phase 2)** for the bid queue. **PubSubTopic migration (Phase 4)** for live-bid feeds. **BlindedQueue migration (Phase 6)** for the private-Vickrey variant. **`Effect::BindBlob` (Phase 8)** for the artwork image. |
| `privacy-voting` | **BlindedQueue migration (Phase 6)** for the commit queue — this is the *canonical* BlindedQueue user. **PubSubTopic migration (Phase 4)** for tally publication. The full-feature build is gated on Phase 6. |
| `compute-exchange` | **ProgrammableQueue migration (Phase 2)**, **RelayOperator migration (Phase 5)**, **BlindedQueue migration (Phase 6)**, **PubSubTopic migration (Phase 4)**. The "integration test that lights up every storage primitive." Unblocked at Phase 6. |

**The critical-path observation:** ProgrammableQueue (Phase 2) and
CapInbox (Phase 3) unblock **all** starbridge-apps. BlindedQueue
(Phase 6) is required by three (bounty, gallery's Vickrey,
privacy-voting). The other migrations unblock specific features but
none are pure prerequisites.

**Practical implementation order:**

1. Land Phases 0-1 (slot caveats v1 + WitnessedPredicate module).
2. Land Phase 2 (ProgrammableQueue → proof-of-pattern, no app
   immediately needs it but the architectural shape clicks into
   place).
3. Land Phase 3 (CapInbox) and start subscription's migration
   in parallel.
4. Land Phase 4 (PubSubTopic) and start identity's migration.
5. Land Phase 6 (BlindedQueue) and start privacy-voting's migration.
6. Land Phase 5 (RelayOperator) when DFA lane lands.
7. Cleanups (Phases 7-9) follow whenever convenient.

The shape of the migration is **deletion-heavy**, **app-unblocking**,
and **architecturally clarifying**: the storage crate stops being a
parallel enforcement surface and becomes a thin re-export of the
cell-program patterns its data structures already support.

---

## §10. Honest closing

What this migration **doesn't** fix:

1. **Per-message body delivery** — bodies still ride on `EmitEvent`
   data (cleartext-inside the federation) or out-of-band
   ciphertext-with-content-hash. Deployment choice, not algebra.
2. **Throughput** — turn-mediated queues are slower than
   operator-side queues. Trades latency for verifiability;
   `Effect::QueueAtomicTx` batching is the mitigation.
3. **The Pipeline / dataflow primitive** (`storage::dataflow::Pipeline`)
   stays; it composes the migrated cell-program queues.
4. **`Effect::QueuePipelineStep`** routing-enforcement gap stays
   gated on the DFA lane.
5. **Queue cell `fields[1]` migration** (length → Merkle root, per
   audit Q4.2) is required as part of Phase 2 and is breaking.
6. **Apps not in the starbridge plan** (amm, lending, orderbook,
   stablecoin, dao-treasury, prediction-market) are deleted, not
   migrated.
7. **Backward compatibility** — the migration is breaking at the
   storage-crate API level; major-version bump.
8. **The `Custom` constraint escape** is honest about cross-slot
   gaps but harder to audit than named variants until
   `FieldLteOther` lands (Open Q §7.2).
9. **No new privacy guarantees** — preserves existing boundary
   contracts per `BOUNDARIES.md`; about enforcement venue, not
   about what's hidden from whom.
10. **The migration won't run itself** — recipe, not implementation.
    ~3-month timeline assumes one focused team.

What this migration **does** fix:

- The architectural confusion that storage primitives are a parallel
  system.
- The authorization gap (subscription CLAUDIT §P0-5).
- The audit-trail gap: every operation produces a `TurnReceipt`.
- The double enforcement loop.
- The effect-bloat trajectory.
- The factory abstraction's unused-ness.

The shape of the migration is the shape of the unification: storage
primitives, slot caveats, witnessed predicates, factories, and the
executor's evaluator are the same algebraic object viewed from
different sides. Naming the object — the cell-program pattern — is
the precondition to seeing that everything else was already in
place.

---

## §11. Cited file pointers

Code:
- `cell/src/factory.rs:163-197` — `FactoryDescriptor`.
- `cell/src/factory.rs:180-192` — `state_constraints` field doc.
- `cell/src/program.rs:223-397` — `StateConstraint` (post-Lane-G).
- `turn/src/action.rs:625-634` — `Effect::CreateCellFromFactory`.
- `turn/src/executor.rs:7100-7125` — factory effect executor branch.
- `turn/src/executor.rs:4020-4024` — cell-program evaluation site.
- `circuit/src/effect_vm.rs:864-880` — factory AIR selector.
- `extension/src/page.ts` — `createFromFactory`, `verifyProvenance`
  (per `STARBRIDGE-APPS-PLAN.md §1.3`).
- `storage/src/inbox.rs:1-588` — `CapInbox`.
- `storage/src/programmable.rs:30-36` — Phase 1 type alias to
  `cell::program::StateConstraint`.
- `storage/src/programmable.rs:60-580` — `QueueConstraint` enum +
  evaluator.
- `storage/src/pubsub.rs:1-531` — `PubSubTopic`.
- `storage/src/blinded.rs:1-980` — `BlindedQueue`.
- `storage/src/operator.rs:1-738` — `RelayOperator`.
- `storage/src/relay.rs:1-365` — store-and-forward.
- `storage/src/namespace_mount.rs:1-466` — `StorageMount`.
- `storage/src/content.rs:1-188` — `ContentStore`.
- `app-framework/src/inbox_endpoint.rs:113` — HTTP shim.
- `apps/subscription/src/delivery.rs:138` — `CapInbox::receive_at`.

Design docs:
- `SLOT-CAVEATS-DESIGN.md` — the 21-variant slot caveat lift.
- `SLOT-CAVEATS-EVALUATION.md` — coverage critique, gaps named.
- `PREDICATE-INVENTORY.md` — every predicate kind, `WitnessedPredicate`
  unification.
- `STORAGE-REFLECTIVITY-RBG-DFA-AUDIT.md` — the storage / RBG / DFA
  audit; Q4.2 promotion targets.
- `BOUNDARIES.md` — populations vocabulary (cleartext-inside /
  commitment-inside / acceptance-inside / out-of-band).
- `CELL-CRATE-REVIEW.md` — cell layer status.
- `STARBRIDGE-APPS-PLAN.md` — the apps consuming the migration.
- `DESIGN-max-custom-effects.md` — the `Custom { vk_hash }` shape
  used by `WitnessedPredicate::Custom`.
- `APPS-AS-USERSPACE-AUDIT.md` — the 16-primitive Tier-1/2/3 ranking
  (#10, #11, #12, #15 are storage-side).
- `DFA-RATIONALIZATION-DESIGN.md` — DFA lane, integrated with
  RelayOperator (§3.5) and PubSubTopic topic filters.
