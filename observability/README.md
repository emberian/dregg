# pyana-observability

Studio-shape trace event emitter for the pyana turn substrate.

## What it does

`pyana-observability` is **two things** in one crate:

1. **A library** (`pyana_observability`) exposing typed trace event types and
   an in-process emitter. Other crates can construct `TraceEvent` values and
   push them onto an `EventLog` without taking on a tracing dependency.
2. **A binary** (`pyana-observability`) that runs a **tour**: constructs a
   scenario exercising every event variant the Studio inspector cares
   about, executes a real `TurnExecutor` against an in-memory `Ledger`,
   and emits a single JSON document on stdout containing the full event
   log in emission order.

## Run

```
cargo run -p pyana-observability > /tmp/trace.json
cargo run -p pyana-observability | jq '.events | length'
cargo run -p pyana-observability | jq '.events[].kind' | sort | uniq -c
```

## JSON schema (v1 — `pyana-observability-event-stream-v1`)

### Top level

```json
{
  "schema_version": 1,
  "schema_name":    "pyana-observability-event-stream-v1",
  "event_count":    <usize>,
  "events":         [ <TraceEvent>, ... ]
}
```

The order of `events[]` is the order in which they were emitted. Each event
also carries `envelope.seq`, a monotonic counter starting at 0; pairs of
events with the same `timestamp` may be ordered using `seq`.

### Event shape

Every event is:

```json
{
  "kind":     "<discriminator>",
  "envelope": { ... cross-cutting context ... },
  "payload":  { ... variant body ... }
}
```

`kind` is one of:

| kind                          | meaning                                              |
|-------------------------------|------------------------------------------------------|
| `authorization`               | an `Authorization` variant was observed              |
| `sovereign_witness_verified`  | a sovereign-cell witness was verified                |
| `state_constraint_evaluated`  | a slot caveat (`StateConstraint`) was evaluated      |
| `bilateral_receipt`           | one γ.2 bilateral entry was folded into a root       |
| `bilateral_rollup`            | per-cell roll-up of the seven-direction γ.2 PI       |
| `federation`                  | federation join / leave / attestation / id-derive    |
| `turn_lifecycle`              | turn submitted / committed / rejected / expired      |

### Envelope

```json
{
  "schema_version": 1,
  "seq":            <u64>,
  "timestamp":      "<ISO-8601 / RFC 3339 UTC>",
  "turn_hash":      "<hex>"  // optional
  "actor":          "<hex>"  // optional CellId
  "federation_id":  "<hex>"  // optional
  "cell_id":        "<hex>"  // optional CellId
}
```

All optional envelope fields are omitted when not applicable (e.g. a
federation `IdDerived` event has no `turn_hash`).

### Per-variant payloads

#### `authorization`

Tag field: `auth_kind`. One of `signature`, `proof`, `breadstuff`, `bearer`,
`unchecked`, `cap_tp_delivered`. Each variant emits:

- `signature`: `r_hex`, `s_hex` (64-char each)
- `proof`: `proof_bytes_hash` (BLAKE3 hex), `proof_bytes_len`, `bound_action`, `bound_resource`
- `breadstuff`: `token_hash`
- `bearer`: `target`, `permissions`, `expires_at`, `revocation_channel?`, `allowed_effects?`, `delegation { delegation_kind: signed_delegation | stark_delegation, ... }`
- `unchecked`: empty payload
- `cap_tp_delivered`: `cert_hash`, `introducer_federation`, `target_federation`, `target_cell`, `recipient_pk`, `introducer_pk`, `sender_pk`, `sender_signature_prefix`, `cert_nonce`, `expires_at?`, `max_uses?`, `permissions`, `allowed_effects?`

**Boundary discipline.** Proof bytes and bearer delegation proof bytes are
hashed before emission — never serialized in full. Bearer signing keys and
introducer secrets never leave the producer.

#### `sovereign_witness_verified`

```json
{
  "cell_id":           "<hex>",
  "sequence":          <u64>,
  "has_stark_proof":   <bool>,
  "old_commitment":    "<hex>",
  "new_commitment":    "<hex>",
  "effects_hash":      "<hex>",
  "witness_timestamp": "<ISO-8601>"
}
```

**Boundary discipline.** Per `BOUNDARIES.md §2.6`, the witness cleartext
(`cell_state`) is cleartext-inside the cell owner. This payload deliberately
omits cleartext slot values, the cell signing key, and the commitment
preimage. Only commitments + `(cell_id, sequence, has_stark_proof)` are
emitted.

#### `state_constraint_evaluated`

```json
{
  "constraint_kind":     "<one of 21 snake_case kinds>",
  "slot_index":          <u8 or null>,
  "extra_slot_indices":  [<u8>, ...]  // omitted when empty
  "accepted":            <bool>,
  "reason":              "<string>"   // omitted when accepted == true
}
```

`constraint_kind` values: `field_equals`, `field_gte`, `field_lte`,
`sum_equals`, `write_once`, `immutable`, `monotonic`, `strict_monotonic`,
`bounded_by`, `field_delta`, `field_delta_in_range`, `field_gte_height`,
`field_lte_height`, `sum_equals_across`, `sender_authorized`,
`capability_uniqueness`, `rate_limit`, `rate_limit_by_sum`, `temporal_gate`,
`preimage_gate`, `monotonic_sequence`, `allowed_transitions`,
`temporal_predicate`, `bound_delta`, `any_of`, `custom`.

**Boundary discipline.** The cleartext slot value is never emitted — only
the constraint kind, slot index, and the structured rejection reason
(which is the executor's public error path).

#### `bilateral_receipt`

```json
{
  "direction":         "<one of seven>",
  "transfer_id":       "<hex; 4 BabyBears = 16 bytes = 32 hex chars>",
  "peer_cell_id":      "<hex; CellId>",
  "accumulator_root":  "<hex; 4 BabyBears>",
  "amount":            <u64 or absent>
}
```

`direction` is one of `outbound_transfer`, `inbound_transfer`,
`outbound_grant`, `inbound_grant`, `intro_as_introducer`,
`intro_as_recipient`, `intro_as_target` — mirroring the seven PI count
slots from `bilateral_schedule::BilateralCounts`.

`amount` is present only for transfers.

#### `bilateral_rollup`

```json
{
  "counts": { outbound_transfer, inbound_transfer, outbound_grant, inbound_grant, intro_as_introducer, intro_as_recipient, intro_as_target },
  "roots":  { outgoing_transfer, incoming_transfer, outgoing_grant, incoming_grant, intro_as_introducer, intro_as_recipient, intro_as_target }
}
```

Each root is the hex packing of a `[BabyBear; 4]` (32 hex chars). The
counts are u32 frequencies of each direction.

#### `federation`

Tag field: `event`. One of `id_derived`, `member_joined`, `member_left`,
`attestation`. Payload shapes:

- `id_derived`: `federation_id`, `epoch`, `threshold`, `member_count`, `members[]`
- `member_joined` / `member_left`: `federation_id_before`, `federation_id_after`, `epoch_after`, `member_pk`
- `attestation`: `federation_id`, `epoch`, `message_hash`, `signer_count`, `attestation_kind` (`bls` | `ed25519` | `mixed`)

#### `turn_lifecycle`

Tag field: `phase`. One of `submitted`, `committed`, `rejected`, `expired`, `pending`.

- `submitted`: `nonce`, `fee`, `action_count`, `valid_until?`, `previous_receipt_hash?`
- `committed`: `receipt_hash`, `forest_hash`, `pre_state_hash`, `post_state_hash`, `effects_hash`, `timestamp`, `action_count`, `computrons_used`, `finality`
- `rejected`: `reason`, `at_action?`
- `expired`: empty payload
- `pending`: `waiting_on`

## Replay-friendliness

Each event is self-contained. To reconstruct a timeline:

1. Group events by `envelope.turn_hash` to form per-turn slices.
2. Within each slice, sort by `envelope.seq` to recover emission order.
3. The `bilateral_rollup` event closes a turn's bilateral story; the
   per-cell `counts` + `roots` match the PI vector the γ.2 AIR binds.
4. The `turn_lifecycle.committed` event carries the canonical receipt
   hashes — link it to the actual `TurnReceipt` artifact out of band.

An external tool can re-derive the bilateral roots from the
`bilateral_receipt` per-entry events alone (each carries the post-fold
root for its direction), without consulting any other state.

## Library API

```rust
use pyana_observability::{Emitter, TraceEvent, EventEnvelope};
use pyana_observability::events::{EventBody, AuthorizationPayload};

let em = Emitter::new();
let (seq, ts) = em.next_envelope_seed();
em.emit(TraceEvent::Authorization(EventBody {
    envelope: EventEnvelope::new(seq, ts).with_turn_hash(&turn_hash),
    payload: AuthorizationPayload::from_authorization(&auth),
}));
println!("{}", em.snapshot().to_pretty_string());
```

## Hex / time conventions

- **Hashes / commitments / pubkeys**: 32 bytes → 64 lowercase hex chars,
  no `0x` prefix.
- **Bilateral roots / IDs**: 4 × `BabyBear` (each `u32` LE) → 16 bytes → 32
  lowercase hex chars.
- **Timestamps**: ISO 8601 / RFC 3339 UTC with millisecond precision,
  e.g. `2026-05-24T12:34:56.789Z`.

## Boundary discipline (`BOUNDARIES.md` compliance)

This crate emits only what is **acceptance-inside** or **commitment-inside**
the world outside the cell owner. Concretely:

- No cleartext cell state, slot values, or commitment preimages.
- No private keys, no full bearer-cap delegation proofs, no full STARK
  proof bytes (only their BLAKE3 hash and length).
- Authorization payloads emit certificate hashes, public keys, and the
  recipient's signature prefix — never the introducer's private key.
- The sovereign witness payload emits `(cell_id, sequence,
  has_stark_proof)` plus public commitments — never the witness cleartext.

## What is **not** here (yet)

1. **Hook calls in other crates.** The library API exists; integration
   points in `turn/`, `cell/`, `federation/`, `wire/`, etc. are not yet
   wired (the lanes that own those crates are mid-refactor; touching them
   here is out of scope per the brief). The tour binary synthesises events
   itself rather than driving them through the executor.
2. **Persistent log.** Events live in memory; a write-to-disk / WAL
   surface is future work.
3. **Concurrent emission.** `Emitter` is `Rc<RefCell<_>>` — single-threaded
   per process. A multi-thread emitter would swap in `Arc<Mutex<_>>` (or a
   lock-free channel) without changing the public types.
4. **Effect-VM trace emission.** The old single-document JSON dump
   bundled the Effect VM trace; the new event stream does not. A future
   `air_trace` event variant would close this.
