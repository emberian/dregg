# starbridge-subscription

> **The first concrete proof-of-pattern for `STORAGE-AS-CELL-PROGRAMS.md`.**
> A `CapInbox`-shaped subscription queue rebuilt as a starbridge-app:
> `FactoryDescriptor` + operation-scoped `CellProgram::Cases(_)` +
> turn-builders that compose only existing `Effect` variants.

## Overview

A **subscription cell** is a publisher/consumer message queue whose
slot layout, slot caveats, and per-method operation-scoping live in a
[`subscription_factory_descriptor`][1] anyone can audit by hashing.
Publish, consume, and the two grant operations are
[`AppCipherclerk`][2]-signed `Action`s composed entirely of existing
`Effect::SetField` and `Effect::EmitEvent` variants. There is no new
`Effect` variant; there is no operator-side enforcement loop.

This crate is **storage-as-cell-programs in action.** Compare against
the operator-side `dregg_storage::programmable::ProgrammableQueue` it
succeeds:

| Surface | `storage::programmable::ProgrammableQueue` | `starbridge-subscription` |
|---|---|---|
| **Where invariants live** | `storage::programmable::QueueProgram::evaluate_constraint` — an operator-process Rust evaluator | `dregg_cell::CellProgram::evaluate_with_meta` — the same per-turn evaluator the executor runs over every cell |
| **Who enforces** | A storage-side closed-enum (`QueueConstraint::*`) | The executor's slot-caveat vocabulary (`StateConstraint::*`) |
| **What produces a receipt** | Nothing — appends are operator commitments | Every turn produces a `TurnReceipt` and (for sovereign cells) a `WitnessedReceipt` |
| **How "only authorized senders may publish" is enforced** | A `QueueConstraint::SenderAuthorized` check inside the storage-process | A `StateConstraint::SenderAuthorized { set: PublicRoot { set_root_index: 3 } }` in the cell-program; executor rejects on every turn |
| **How "head advances by exactly +1" is enforced** | A `MonotonicSequence` variant in the storage evaluator | A `StateConstraint::MonotonicSequence { seq_index: 0 }` in the cell-program |
| **Where operation-scoping lives** | Implicit in which HTTP endpoint the request hit | Explicit `CellProgram::Cases(_)` with `TransitionGuard::MethodIs { method: symbol("publish") }` — *one* program, four cases, default-deny on unknown methods |
| **New `Effect` variants introduced** | `Effect::QueueAllocate / Enqueue / Dequeue / Resize / AtomicTx / PipelineStep` (six) | Zero |
| **AppCipherclerk signature surface** | An ad-hoc `sender_hex` field on the HTTP request body | A real `Authorization::Signature(..)` produced by `AppCipherclerk::make_action` |

The "two enforcement loops" failure mode named in
`STORAGE-AS-CELL-PROGRAMS.md` §1 — `QueueConstraint` evaluating in
operator-Rust, `StateConstraint` evaluating in executor — collapses
to one. **There is only `StateConstraint`.** The
storage primitive's enforcement role evaporates into a thin
content-store for the (off-slot) message payloads.

## The slot layout

`STATE_SLOTS = 8`:

| Slot | Name | Lifetime caveat | Operation-scoped caveats |
|---:|---|---|---|
| 0 | `seq_head` | `Monotonic` | `MonotonicSequence` under `publish`; `Immutable` under `consume` / `grant_*` |
| 1 | `seq_tail` | `Monotonic` | `MonotonicSequence` under `consume`; `Immutable` under `publish` / `grant_*` |
| 2 | `capacity` | `Immutable` | (frozen everywhere) |
| 3 | `authorized_publishers_root` | opaque commitment | changed + non-zero under `grant_publisher`; `Immutable` everywhere else |
| 4 | `authorized_consumers_root` | opaque commitment | changed + non-zero under `grant_consumer`; `Immutable` everywhere else |
| 5 | `owner_pk_hash` | `Immutable` | (frozen everywhere) |
| 6 | `message_root` | opaque commitment | changed + non-zero under `publish`; `Immutable` under `consume` / `grant_*` |
| 7 | `latest_payload_hash` | — | overwritten under `publish`; `Immutable` under `consume` / `grant_*` |

### Why `message_root` (a root commitment) and not per-message slots?

The reference design in `STORAGE-AS-CELL-PROGRAMS.md` §3.1 sketches
per-message `WriteOnce` slots as the *idealized* shape. Cells have
only 8 slots total, which can't host an unbounded message ring. The
real data path is the same one `MerkleQueue::root` uses today in
`dregg_storage`: a Poseidon2/BLAKE3 root commitment in slot 6, with
the per-message `(seq, payload_hash)` tuples stored out-of-band in a
content-addressed store keyed by the root.

The `WriteOnce`-at-the-individual-message-level semantic still holds
— it's structurally enforced by the root: once `(i, payload_hash)` has
been folded into the root, the root commits to that payload at
position `i`, and a forgery would have to produce the same root
(rejected by the consumer's Merkle membership check). At the slot
level, the program treats roots as opaque commitments: the operation
that owns a root requires it to change and remain non-zero, while all
other operations freeze it.

For deployments where the message ring is tiny and slot-resident (no
off-cell store), the `message_root` slot can be replaced by a fixed
set of `WriteOnce { index: k }` constraints over slots 6..N. That's a
follow-on; the root-commitment shape is the canonical pattern.

## Operations

Each operation is a turn-builder that produces an `AppCipherclerk`-signed
`Action` whose method symbol the cell-program dispatches against.

### `publish` — [`build_publish_action`][3]

```rust
let action = build_publish_action(
    &cclerk,
    subscription_cell,
    /* new_head        */ u64_field(old_head + 1),
    /* new_message_root */ poseidon2(&[&old_root, &(new_head, payload_hash)]),
    /* payload_hash    */ payload_hash,
);
```

Effects: three `SetField` (slots 0, 6, 7) + one `EmitEvent`. The
publish-case constraints enforce:
- head advances by exactly +1 (`MonotonicSequence`);
- tail is immutable (no co-advance bypass);
- message_root changes and remains non-zero;
- sender is in `authorized_publishers_root` (`SenderAuthorized`);
- membership roots stay frozen.

### `consume` — [`build_consume_action`][4]

```rust
let action = build_consume_action(
    &cclerk,
    subscription_cell,
    /* new_tail              */ u64_field(old_tail + 1),
    /* consumed_payload_hash */ payload_hash,
);
```

Effects: one `SetField` (slot 1) + one `EmitEvent`. The consume-case
constraints enforce:
- tail advances by exactly +1 (`MonotonicSequence`);
- head, message_root, latest_payload all immutable;
- membership roots immutable;
- sender is in `authorized_consumers_root` (`SenderAuthorized`).

### `grant_publisher` / `grant_consumer` — [`build_grant_publisher_action`][5] / [`build_grant_consumer_action`][6]

```rust
let action = build_grant_publisher_action(
    &cclerk, // owner
    subscription_cell,
    /* new_publishers_root */ poseidon2(&[&old_root, &new_publisher_pk]),
    /* new_publisher_pk    */ new_publisher_pk,
);
```

Effects: one `SetField` (slot 3 or 4) + one `EmitEvent`. The grant-case
constraints enforce:
- the targeted membership root changes and remains non-zero;
- every other slot stays frozen.

The "only owner may grant" rule rides on the per-cell capability
layer: the action's sender must hold the owner cap (whose preimage
is committed in slot 5). That's enforced by the executor's capability
machinery, not the slot-caveat evaluator.

## Adversarial coverage

`tests/program.rs` drives `CellProgram::evaluate_with_meta` directly
against hand-rolled `(old, new, meta)` triples, covering:

- **Round-trip** `publish → consume` preserves the payload hash.
- **Non-authorized publisher / consumer** → rejected
  (`SenderAuthorized` requires an executor-bound membership witness;
  the unit-test path observes the constraint's hard rejection without
  one).
- **Rewrite of `message_root` under `consume`** → rejected (`Immutable`).
- **Rewrite of `latest_payload` under `consume`** → rejected.
- **No-op or zero `message_root` under `publish`** → rejected
  (changed+non-zero opaque-root invariant).
- **Head / tail decrement** → rejected (`MonotonicSequence`).
- **Head `+= 2`** → rejected (`MonotonicSequence` requires exactly `+1`).
- **Publish advances tail** → rejected (`Immutable` on slot 1 in the
  publish case).
- **Consume advances head** → rejected (`Immutable` on slot 0 in the
  consume case).
- **Capacity / owner mutation** → rejected (Always-case `Immutable`).
- **Unknown method symbol** → rejected (`NoTransitionCaseMatched` —
  Cav-Codex Block 4 default-deny).
- **`grant_consumer` touches publishers root** → rejected.
- **`grant_publisher` leaves publishers root unchanged or zeroes it** →
  rejected (changed+non-zero opaque-root invariant).

Run:

```sh
cargo test -p starbridge-subscription
```

## Composition with `dregg-directory`

A subscription cell can be looked up by name. The intended pattern is
the same one nameservice exposes today: publish the subscription's
`CellId` as the resolution target of a name in `dregg-directory`,
e.g. `dregg://name/feeds.alice.weekly-update`. Consumers resolve the
name (one round-trip), then mount `<dregg-subscription-feed
uri="...">` against the resolved cell.

We sketch but don't wire the integration here — the directory mount
is in `starbridge-apps/nameservice/`; this crate is the queue
primitive that nameservice points to. Wiring is a few lines at the
host bootstrap once both apps are registered on the same
`StarbridgeAppContext`:

```rust
let ctx = StarbridgeAppContext::new(cclerk, executor);
starbridge_nameservice::register(&ctx);
starbridge_subscription::register(&ctx);
// host serves both factory descriptors + inspector descriptors
```

The site's Studio surface can then mount `<dregg-name>` and
`<dregg-subscription>` against the same context, and the directory
inspector links into subscription inspectors by URI.

## Dependency on the caveat-correctness lane

`STORAGE-AS-CELL-PROGRAMS.md` notes the operation-scoped
`CellProgram::Cases(_)` shape — specifically `TransitionGuard::MethodIs`
matching against the action's method symbol, plus default-deny on no
match — is exactly what the caveat-correctness lane is adding. If
that lane has not landed at the executor / AIR level by the time this
crate ships:

- The `FactoryDescriptor`, turn-builders, and `subscription_program`
  are all correct in shape and produce real Actions with real
  signatures.
- The unit tests in `src/lib.rs` and adversarial tests in
  `tests/program.rs` drive `CellProgram::evaluate_with_meta(..)`
  directly, so they exercise the operation-scoped semantics regardless
  of the executor's wiring state.
- **What waits on the lane** is the *executor-side* enforcement
  during actual turn submission — the path where a malicious action
  routes through the executor's `evaluate_cell_program` call. Until
  the lane lands, that path may not honor `MethodIs` guards.
- **What waits on the AIR** is the in-circuit enforcement (so a
  STARK over a subscription cell's lifetime is bound by the
  operation-scoped shape, not just the flat invariants).

The crate-level tests do not depend on the lane landing; the
end-to-end turn submission path does.

## What this replaces

Per `STORAGE-AS-CELL-PROGRAMS.md` §3.1's "what it replaces":

- **`storage/src/inbox.rs`** (588 LOC) → mostly thin re-exports or
  deletions:
  - `CapInbox::new` → cclerk `createFromFactory(SUBSCRIPTION_FACTORY_VK, ..)`.
  - `CapInbox::receive` / `receive_at` →
    [`build_publish_action`][3].
  - `CapInbox::dequeue` / `read_next` →
    [`build_consume_action`][4].
  - `CapInbox::status` → reading `cell.state.public_field_view()` for
    slots 0, 1, 2.
- **`app-framework/src/inbox_endpoint.rs`** → a thin
  Action-producing shim (the HTTP surface translates
  `POST /subscription/publish` into a signed `Action` and posts to
  the executor; no enforcement lives there).
- **`apps/subscription/src/delivery.rs:138`** — the `receive_at` call
  in the legacy subscription app — collapses into the same cclerk
  `make_action` call shown in the operations section above.

Net LOC delta per `STORAGE-AS-CELL-PROGRAMS.md` §3.1: **~−400 in
storage, ~+200 in cell-program + factory deployment, ~−300 in
app-framework. Net ~−500 LOC across the migration.**

## Pages

The `pages/index.html` mounts a `<dregg-app>` with the three
inspector kinds this crate registers:

- `<dregg-subscription uri="...">` — display a subscription's state
  (head, tail, capacity, latest payload, plus the membership roots).
- `<dregg-subscription-publish-form>` — publisher's compose-and-send
  UI; uses the `publish` turn-builder via the extension cipherclerk's
  `signTurn` bridge.
- `<dregg-subscription-feed>` — consumer's live feed; subscribes to
  `subscription-published` events from a target cell and (on consume)
  emits a `consume` turn.

The JS-side surface lives under `starbridge-apps/shared/` per the
nameservice precedent.

`pages/turn-builders.js` exposes the JS counterparts of the Rust
turn-builders, registered under `window.dregg.builders.subscription`:

```js
await window.dregg.builders.subscription.publish(subscriptionUri, "hello world");
await window.dregg.builders.subscription.consume(subscriptionUri);
await window.dregg.builders.subscription.grant_publisher(subscriptionUri, newPubkeyBytes);
await window.dregg.builders.subscription.grant_consumer(subscriptionUri, newPubkeyBytes);
```

Each helper reads the cell to compute the next sequence number / root,
assembles the `turnSpec` (same shape the Rust `build_*_action` helpers
produce), and dispatches through `window.dregg.signTurn(..)`. Policy
stays in Rust — the JS shim only encodes shape.

[1]: src/lib.rs#L235
[2]: ../../app-framework/src/cipherclerk.rs
[3]: src/lib.rs#L375
[4]: src/lib.rs#L417
[5]: src/lib.rs#L463
[6]: src/lib.rs#L495
