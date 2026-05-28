# STORAGE-SECONDARIES-TRIAGE

Per audit task 3 of the 2026-05-25 lane-honesty sweep. Classifies every
module under `storage/src/` as:

- **template-candidate** — should migrate into `dregg-storage-templates`
  as a `FactoryDescriptor` with executor-enforced `CellProgram::Cases`,
  matching the existing 5 templates (`cap_inbox`, `programmable_queue`,
  `pubsub_topic`, `blinded_queue`, `relay_operator`). The legacy
  operator-side enforcement loop is retired and the underlying
  data-structure (usually `MerkleQueue`) remains in `storage/`.
- **substrate** — belongs in `storage/` permanently. These are the
  data-structure primitives the templates compose against (queues, WAL,
  content store, commitments, quotas, cost models) and the
  cross-cutting accounting that has no per-cell program shape.
- **retire** — superseded by an in-tree replacement OR sketched but not
  carrying its weight; can be removed once known callsites switch.

Where a module is listed as **retire**, a `grep` line shows the
non-self, non-test callsites surveyed. Removal is conditional on those
sites migrating; no migration code is shipped in this lane (doc only).

The migration table in `storage/src/lib.rs:1..25` already commits to
five of the deprecated modules; this doc covers the rest.

---

## atomic.rs — `QueueTransaction`

**Classification:** template-candidate.

**Justification.** Cross-queue atomic commit is exactly the surface a
"transactional queue group" cell-program template would expose: a
`begin / enqueue(q_i, payload) | dequeue(q_j) / commit` op-sequence is
declarative, and the all-or-nothing invariant is naturally
`CellProgram::Cases { commit: state_constraints_that_apply_all_ops,
abort: state_unchanged_constraint }`. Today the enforcement is in the
operator-side `QueueTransaction::commit_2pc` loop; replacing it with
executor-enforced cases gives the same coverage without a parallel
trust path.

**Sketch.**

- Template: `dregg_storage_templates::atomic_queue_group`.
- Factory descriptor: `atomic_queue_group_factory_descriptor()` taking
  the participating queue ids as factory args.
- Slot shape: `participants: [CellId; N]`, `pending_ops_root: [u8; 32]`,
  `epoch: u64`, `tx_log_root: [u8; 32]`.
- Key state transitions: (a) `BeginTx` → bumps epoch, sets
  `pending_ops_root`; (b) `AppendOp` → witnesses a single op against
  the participant's existing cell program; (c) `Commit` → enforces
  every pending op's cell-program constraint as a `CellProgram::Cases`
  match in a single turn; (d) `Abort` → asserts `pending_ops_root`
  cleared and per-participant state unchanged from epoch-start.
- The 2PC dance becomes structural: the `Commit` case predicates
  succeed iff every participant's per-op constraint succeeds, modelled
  as `WitnessedPredicate::Conjunction` in the case row.

## blinded.rs — `BlindedQueue`

**Classification:** template-candidate (in flight, already deprecated).

**Justification.** Already documented as deprecated in favor of
`dregg_storage_templates::blinded_queue`. The migration table in
`storage/src/lib.rs` commits this row. No further triage needed.

## commitment.rs — typed Blake3/Poseidon2 commitment framework

**Classification:** substrate.

**Justification.** This is the cross-cutting field-domain commitment
plumbing the templates and the verifier-AIR boundary both consume. It
has no per-cell program shape — it is the encoding layer the templates
build on (e.g. `BlindedQueue::commit_blob` produces a typed dual-form
commitment that becomes the cell-program slot value). Belongs in
`storage/` permanently.

## content.rs — `ContentStore` (blob store with quota)

**Classification:** substrate.

**Justification.** A content-addressed blob store with quota-debit on
write is a data-structure primitive that several cell templates would
share. Templating it would force every store reference to instantiate
a cell, which inverts the relationship: `ContentStore` is what
`cap_inbox` / `relay_operator` / `blinded_queue` store blobs INTO. The
quota-cell side (`QuotaCell` in `quota.rs`) is the cell-program
analogue; the blob store itself is substrate.

## dataflow.rs — `Pipeline` queue-to-queue routing

**Classification:** template-candidate.

**Justification.** A "pipeline" is a declarative composition: source
queue → transform → sink queue. The transform predicates are exactly
what `CellProgram::Cases` already declares. Encoding the pipeline as a
cell would let the executor enforce conservation (every entry that
leaves source appears in exactly one sink) per turn, instead of
trusting the operator-side `Pipeline::run` loop.

**Sketch.**

- Template: `dregg_storage_templates::dataflow_pipeline`.
- Factory descriptor: `dataflow_pipeline_factory_descriptor()` taking
  `(source_queue_id, sink_queue_ids[N], stage_descriptions: Vec<StageSpec>)`.
- Slot shape: `source_cursor: u64`, `sink_cursors: [u64; N]`,
  `forwarded_root: [u8; 32]`, `dropped_root: [u8; 32]` (entries the
  filter rejected; persisted for audit).
- Key state transitions: (a) `Advance` → witnesses a batch of
  consecutive source-queue dequeues against the stage predicates, and
  proves each surviving entry's `sink_index` matches the routing
  function; conservation case asserts `Δforwarded + Δdropped ==
  Δsource_cursor`. (b) `RetireStage` (governance) → asserts the
  template's stage spec unchanged unless an authorising signature is
  in the call_forest.

## dedup.rs — `DeduplicationFilter`

**Classification:** retire (after migration sweep).

**Justification.** The `pubsub_topic` template already folds this into
slot 7 (per `dregg-storage-templates/src/pubsub_topic.rs:34`). The only
non-template, non-template-doc consumer is
`preflight/src/checks/storage.rs:4`. Once preflight is updated to
either read the slot directly or to drop its dedup smoke-check (it is
a one-off integration sanity test), this file can be removed.

```
$ grep -rn 'use dregg_storage::dedup' --include='*.rs'
  dregg-storage-templates/src/pubsub_topic.rs (doc only)
  preflight/src/checks/storage.rs:4
```

## erasure.rs — XOR/RS erasure coding

**Classification:** substrate.

**Justification.** Erasure coding is a cryptographic primitive for
availability sampling; it has no per-cell program shape. The blob
store consumes it (a blob is stored as N chunks, any K reconstruct);
making it a cell would invert the dependency.

NOTE: the module header itself warns the implementation is "a
simplified prototype using XOR-based coding (not full Reed-Solomon)".
Hardening this to a real RS library is orthogonal to the
template-vs-substrate question.

## inbox.rs — `CapInbox`

**Classification:** template-candidate (already migrated and
deprecated). The `cap_inbox` template covers it; the migration table
in `storage/src/lib.rs` commits the row.

## metering.rs — computron cost model

**Classification:** substrate.

**Justification.** Cost-model policy that the templates and the
quota-cell program both consume. It is configuration, not a
state-bearing primitive — `CostPolicy` is plain data, not a cell.

## multi_asset.rs — `FeePolicy` / `ExchangeRate`

**Classification:** template-candidate (governance / oracle slice).

**Justification.** The fee policy itself is policy data (substrate),
but the **rate-publication** flow — "an oracle cell holds the current
asset → computron exchange rate, gated by an oracle-signature
constraint, and other cells consume it as a cap reference" — is a
canonical cell-program shape. Today `FeePolicy::update_rate` is a
plain method; promoting it to a `rate_oracle` template with executor-
enforced governance is the honest move.

The plain-data `FeePolicy` itself stays as a substrate type the
oracle's slot holds.

**Sketch.**

- Template: `dregg_storage_templates::rate_oracle`.
- Factory descriptor: `rate_oracle_factory_descriptor()` taking
  the trusted publisher signature set + a denominator asset id.
- Slot shape: `current_rates: BlindedSet<AssetId, ExchangeRate>`,
  `published_at_epoch: u64`, `publisher_set_commitment: [u8; 32]`.
- Key state transitions: `Publish` (gated by
  `AuthorizedSet::Threshold { publishers, k }`) sets new rates and
  bumps epoch; `Read` is a free off-chain query.

## namespace_mount.rs — `StorageMount`

**Classification:** template-candidate.

**Justification.** Mounting an inbox or topic under a namespace path
with a fee policy and write whitelist is *exactly* the directory cell
shape. The governance/quota/whitelist invariants are declarable;
today they're operator-side fields on a struct. Pairing this with the
existing `nameservice` patterns in `apps/` would unify the mount
surface.

**Sketch.**

- Template: `dregg_storage_templates::namespace_mount`.
- Factory descriptor: `namespace_mount_factory_descriptor()` taking
  `(parent_namespace_cell, path, kind: StorageMountKind, fee_policy_oracle_cell)`.
- Slot shape: `path_canonical: [u8; 32]`, `target_cell: CellId`,
  `fee_policy_oracle: CellId`, `write_authorization:
  AuthorizationSetCommitment`.
- Key state transitions: `Mount` (gated by parent-namespace
  authorisation) registers the mount; `Unmount` (gated by namespace
  governance) clears it; `Write` (per turn from a writer) delegates
  fee-debit and authorization checks to the linked oracle and the
  per-mount `AuthorizationSet`.

## operator.rs — `RelayOperator`

**Classification:** template-candidate (already migrated and
deprecated). Covered by `dregg_storage_templates::relay_operator`.

## poly_queue.rs — `PolyQueue` (KZG10-committed queue)

**Classification:** substrate.

**Justification.** Cryptographic data-structure primitive: queue
state committed as a univariate polynomial with KZG opening proofs.
This is the algebraic substrate a future "succinct-opening queue"
template would commit *to*, not a per-cell program shape itself. The
implementation is feature-gated (`kzg`) and currently consumed only
by future Plonky3/Kimchi recursion work.

## programmable.rs — `ProgrammableQueue`

**Classification:** template-candidate (already migrated and
deprecated). Covered by `dregg_storage_templates::programmable_queue`.

## pubsub.rs — `PubSubTopic`

**Classification:** template-candidate (already migrated and
deprecated). Covered by `dregg_storage_templates::pubsub_topic`.

## queue.rs — `MerkleQueue`

**Classification:** substrate (CANONICAL — DO NOT TEMPLATE).

**Justification.** The Merkle queue IS the universal append-only ring
that the five existing templates and the four new template-candidates
above all build on top of. The lib.rs migration note is explicit:
"the underlying `queue::MerkleQueue` data structure stays — only the
parallel enforcement loop is retired." This is the most-consumed
storage primitive (`teasting/tests/storage_*`, `node/src/relay_service.rs`,
`preflight/src/checks/storage.rs`, every template). Removing or
templating it would force every consumer to round-trip through cell
state for a simple append.

## quota.rs — `QuotaCell` / `SpaceBank`

**Classification:** template-candidate (already a near-template).

**Justification.** `QuotaCell` is conceptually a cell-program already
("bounded counter that decrements on write, refunds on delete"), but
it sits in `storage/` without a `FactoryDescriptor`. Promoting it to
`dregg_storage_templates::quota_cell` would let storage clients
register quota cells through the factory machinery the rest of the
templates use, and would let the executor enforce the byte-cap and
refund-rate invariants declaratively.

**Sketch.**

- Template: `dregg_storage_templates::quota_cell`.
- Factory descriptor: `quota_cell_factory_descriptor()` taking
  `(owner: CellId, initial_quota: u64, byte_cap: u64, refund_rate: u8)`.
- Slot shape: `quota_remaining: u64`, `bytes_used: u64`,
  `refund_rate_basis_points: u32`, `owner_commitment: [u8; 32]`.
- Key state transitions: `Debit { bytes, computrons }` (gated by
  owner-or-delegate authorization) asserts
  `quota_remaining ≥ computrons` and bumps `bytes_used`; `Refund {
  bytes, original_cost }` asserts the originating blob was deleted in
  the same turn (effect-binding-proof) and re-credits a
  `refund_rate`-proportional fraction; `TopUp` re-credits quota from
  a `Transfer { to: this_cell }` effect.

## relay.rs — `MeteredRelay`

**Classification:** template-candidate (already migrated and
deprecated). Folded into `relay_operator`.

## sharding.rs — `ShardedQueue`

**Classification:** template-candidate.

**Justification.** Sharded queue (N physical shards routed by content
hash) is a composition pattern: the shard router cell holds shard
membership and the per-shard cursor advances. The N-shards-per-
logical-queue invariant is exactly `CellProgram::Cases` material:
"enqueue to shard i ⇔ content_hash(payload) % N == i", and conservation
across shards is `Sum(shard_lens) == logical_len`.

**Sketch.**

- Template: `dregg_storage_templates::sharded_queue`.
- Factory descriptor: `sharded_queue_factory_descriptor(num_shards: u8, shard_cells: [CellId; N])`.
- Slot shape: `shard_cells: [CellId; N]`, `total_enqueued: u64`,
  `total_dequeued: u64`, `routing_alg_tag: u32`.
- Key state transitions: `Enqueue` asserts the chosen shard's
  index matches `hash(payload) % N` (a single `CellProgram::Cases`
  predicate); `Dequeue { shard_index }` advances only that shard's
  cursor and bumps `total_dequeued`. The cross-shard conservation
  invariant becomes `WitnessedPredicate::Sum` over the participant
  cells' cursor slots in any audit turn.

## wal.rs — `WriteAheadLog`

**Classification:** substrate.

**Justification.** The WAL is operator-local durability infrastructure
— if the operator's process crashes, on restart it replays the WAL to
reconstruct `MerkleQueue` in-memory state. It is not part of the
per-turn substrate the verifier observes; it is the operator's
recovery story. Promoting it to a cell would not change the trust
story (the operator is still the only one who reads/writes the WAL).
Belongs in `storage/` permanently.

---

## Summary

| module | classification |
|---|---|
| atomic | template-candidate (new: `atomic_queue_group`) |
| blinded | template-candidate (DONE: `blinded_queue`) |
| commitment | substrate |
| content | substrate |
| dataflow | template-candidate (new: `dataflow_pipeline`) |
| dedup | retire (after `preflight` migration) |
| erasure | substrate |
| inbox | template-candidate (DONE: `cap_inbox`) |
| metering | substrate |
| multi_asset | template-candidate (new: `rate_oracle`) |
| namespace_mount | template-candidate (new: `namespace_mount`) |
| operator | template-candidate (DONE: `relay_operator`) |
| poly_queue | substrate |
| programmable | template-candidate (DONE: `programmable_queue`) |
| pubsub | template-candidate (DONE: `pubsub_topic`) |
| queue | substrate (CANONICAL — never template) |
| quota | template-candidate (new: `quota_cell`) |
| relay | template-candidate (DONE: folded into `relay_operator`) |
| sharding | template-candidate (new: `sharded_queue`) |
| wal | substrate |

**Counts:** 5 templated already (DONE), 5 net-new template-candidates
sketched here, 7 substrate, 1 retire pending one downstream
migration.
