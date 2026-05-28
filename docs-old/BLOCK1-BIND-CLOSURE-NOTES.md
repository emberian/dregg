# Block1-Bind Closure Notes

`AIR-SOUNDNESS-AUDIT.md` #71 tracked ~10 `TODO[block1-bind]` sites in
`turn/src/executor/effect_vm_bridge.rs` where the AIR attested vacuous
placeholders (constant `0`, all-zero pubkey, synthetic queue-id alias)
while the executor enforced the real predicate at apply time. The proof
shape was sound only modulo the executor's runtime check — a forged
proof claiming a fake placeholder was indistinguishable from a real
one.

This lane (#71 closure) plumbed `&Ledger` access into
`convert_turn_effects_to_vm` so each projection sources its placeholders
from real ledger state. The table below tracks what closed and what
remains.

## Closed in this lane

| Site | Old placeholder | New binding |
|------|-----------------|-------------|
| `QueueEnqueue.queue_len` | `0` | `ledger.get(queue).state.fields[1]` (u64 LE) |
| `QueueEnqueue.program_vk` | `BabyBear::ZERO` | `hash_to_bb(queue.state.fields[3])` |
| `QueueResize.old_capacity` | `0` | `ledger.get(queue).state.fields[0]` (u64 LE) |
| `QueueAtomicTx.combined_old_root` | `hash_to_bb(cell_id)` | `cell.state.fields[4]` (queue-root slot) |
| `DropRef.current_refcount` | `1` | `ledger.get(cell_id).state.fields[5]` (u32 LE) |
| `ExportSturdyRef.export_counter` | `0` | `ledger.get(target).state.fields[7]` (u32 LE) |
| `EnlivenRef.expected_cell_id` | `hash(swiss, bearer)` | `hash(swiss, bearer, bearer.state.fields[6])` (swiss-table root) |
| `QueueDequeue.expected_message_hash` | `hash(queue_id)` | `hash(queue_id, queue.state.fields[1])` (length-aware) |

These projections now source ledger state, so a malicious prover cannot
substitute arbitrary values — any disagreement with the runtime ledger
surfaces in the AIR's PI matching loop.

## Partially closed (synthetic binding floor)

These sites no longer have a tautological self-loop (the AIR's
constraint is non-trivially anchored to *some* ledger-derived value),
but the load-bearing semantic field still lacks a real ledger source:

### `EnlivenRef.expected_permissions`

The swiss-table entry carries the permissions mask, but reading it
requires a Merkle proof against `bearer.state.fields[6]` (the swiss-
table root). That walk is off-AIR work. Closure path:
- Extend the off-AIR verifier to recover `(expected_cell_id,
  expected_permissions)` from the swiss-table entry via a Merkle
  membership proof.
- Bind the entry's permissions mask into PI alongside the cell-id.

### `ExportSturdyRef.permissions`

The runtime `Effect::ExportSturdyRef { swiss_number, target }` does not
carry the permissions mask. Closure path:
- Extend the runtime variant to `ExportSturdyRef { swiss_number,
  target, permissions }`.
- Plumb through the executor's `apply.rs::ExportSturdyRef` so the
  permissions are explicit at intent-construction time.
- The AIR projection then reads `permissions` directly from the
  variant; no executor synthesis.

## Deferred (requires runtime-variant extension)

### `ValidateHandoff.recipient_pk` and `ValidateHandoff.introducer_pk`

The minimal runtime variant `ValidateHandoff { cert_hash }` carries
only the certificate hash; the recipient and introducer public keys
are recovered from the off-chain certificate at federation-side
verification. The AIR's `aux[0] == hash(cert_hash, hash(recipient_pk,
introducer_pk))` check therefore must rely on synthetic derivation
today.

Closure path: extend the runtime variant to `ValidateHandoff {
cert_hash, recipient_pk, introducer_pk }` and bind both into PI. The
executor's apply path can validate that the certificate's contents
match the carried pks; the AIR then binds them as primary witnesses
rather than synthetic derivations.

## Deferred (requires QueueOperator plumbing)

### `QueueDequeue.expected_message_hash` (full closure)

The dequeue head hash lives in the storage subsystem's
`QueueOperator::queue_head_hash`, not on the queue cell's state. The
current closure mixes the queue length into the synthetic derivation
so two sequential dequeues no longer collide in PI — but the actual
head's cryptographic identity is unbound.

Closure path (architecturally cleanest):
- At enqueue time, fold the message hash into a cell.state slot
  (e.g., `fields[8]` becomes the running queue-head commitment).
- At dequeue time, read the slot from `cell.state.fields[8]` and bind
  it as `expected_message_hash`.

This is a coordinated executor + AIR change because `apply.rs::Queue*`
must maintain the slot, and the AIR's per-row continuity constraint
must witness the slot transition. It is tracked here, not in the lane
that closed the simpler sites.

## How to verify the closure

For each closed site:
1. Construct two ledger states differing only in the targeted field
   (e.g., two queue cells with `fields[1]` set to different lengths).
2. Project both through `convert_turn_effects_to_vm` with the same
   `Effect::Queue*`.
3. Assert the resulting `VmEffect` carries different values for the
   bound projection field.
4. Assert the resulting effects-hash (`compute_effects_hash_4`)
   differs across the two projections.

Pre-closure: both ledger states project to identical `VmEffect`
(placeholder constants drop the ledger signal). Post-closure: the
projections diverge.
