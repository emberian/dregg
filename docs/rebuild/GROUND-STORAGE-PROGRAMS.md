# GROUND-STORAGE-PROGRAMS — the REAL Rust semantics of dregg's cell-storage programs, and the Lean's fidelity to them

> **Scope / method.** Read-only Rust-grounding + design analysis. NO code changed. The mission: establish
> the **Rust** as ground truth for dregg's storage substrate (the data-structure mechanics) and its
> storage-as-cell-programs layer (the migration to factory-minted cell programs), audit the Lean's
> fidelity feature-by-feature, and analyze the "storage-as-cell-programs" generalization against the
> effect-ISA basis. Every claim is cited `file:line`. The user is "not sure the Lean is implemented
> correctly" and wants the **Rust semantics (or a coherently-extrapolated vision) carried forward, NOT a
> Lean fiction**. FID-ESCROW set the precedent: the Lean escrow was a balance-conserving two-cell transfer,
> the Rust is single-cell-debit-into-a-side-table; the Rust won.
>
> **Companion docs read in:** `docs/rebuild/EFFECT-ISA-DESIGN.md` (the orthogonal-basis analysis — the
> 13-CORE recommendation), `docs-old/STORAGE-AS-CELL-PROGRAMS.md` (the migration thesis + per-primitive
> reference designs §3.1–§3.5), `docs/rebuild/REORIENT.md` (the coalgebra direction).

---

## 0. Executive answer

There are **two distinct Rust storage tiers**, and the Lean is faithful to one of them and absent from the
other:

1. **The data-structure substrate** — `storage/` (`MerkleQueue` + WAL durability + computron quota
   metering + Reed-Solomon-shaped erasure coding + content store), `persist/` (the **real** crash-safe
   redb-backed durable store, recovery, checkpoint, pruning, atomic note-spend), `rbg/vfs.rs` (the
   Robigalia Volume/Blob/Directory triple). **This tier is where the advanced features live.** The Lean
   models **none of it** at the byte/durability level: there is **no WAL, no fsync/torn-write recovery, no
   redb, no erasure coding, no Merkle-path dequeue proof, no quota-byte/computron arithmetic** anywhere in
   `metatheory/Dregg2/`. (Verified: `grep` for `wal|erasure|computron|redb|fsync` over the Lean tree
   returns only doc-comment mentions, never a model.) This confirms the prior "~0-20%" audit for the
   substrate.

2. **The storage-as-cell-programs layer** — `dregg-storage-templates/` (the canonical `CapInbox`,
   `ProgrammableQueue`, `PubSubTopic`, `BlindedQueue`, `RelayOperator` as `FactoryDescriptor`s carrying
   `CellProgram::Cases` state machines built from existing `Effect` variants) + `cell/src/program.rs` (the
   74-line `StateConstraint` enum the executor evaluates). **The Lean is genuinely faithful to the
   *shape* of this tier** — `metatheory/Dregg2/Exec/{CapInbox,BlindedQueue,PubSubTopic,RelayOperator,
   Factory,CellProgram,StateMigration}.lean` each model the corresponding template as a `RecordProgram`
   of `StateConstraint`s and prove the right invariants (FIFO `tail ≤ head`, monotone counters,
   conservation, anti-brick migration). It is faithful as a **law-of-the-state-machine** model and
   **honestly flags its own divergences** (name-keyed records vs 8 fixed slots; derived `inflight` vs
   cross-slot relational bound; sender-identity binding deferred).

**The carry-forward verdict.** The storage-as-cell-programs **thesis is correct and the Rust supports it**:
`CapInbox` etc. are genuinely cell-programs-composing-effects (`SetField` + `EmitEvent` + `Transfer`),
NOT bespoke kernel features. The Lean's *law* models are the right thing to carry forward. But three
**Rust semantics are load-bearing and the Lean is a fiction or an overlook** about them, and these must
be carried forward faithfully (§4):
- **(a) the durable WAL + redb crash-safety** (the actual "your data survives a crash" guarantee) — Lean's
  `CellRuntime` "checkpoint/restore/replay" is a pure in-memory `Snapshot` round-trip with **no durability
  content whatsoever**; it proves `restore ∘ checkpoint = id` by `rfl`, which is true of any record and says
  nothing about fsync/torn-writes/recovery.
- **(b) the deposit-accounting + Merkle-ring semantics of the queue** — Lean's `CapInbox` drops the
  `message_root`, `sender_set_root`, and `total_deposits_held` slots entirely (deferred as `-- OPEN:`).
- **(c) the side-table/holding-store as kernel state** — FID-ESCROW already added this for escrow
  (`turn/src/executor/apply.rs:1735`, `EffectsPaired.lean`); the **queue is the same shape** (deposit held
  in a side register, refunded on dequeue) and needs the same honest holding-store model, which `CapInbox.lean`
  currently elides.

---

## 1. The REAL Rust semantics — the data-structure substrate (ground truth)

### 1.1 `MerkleQueue` — content-addressed append-only queue (`storage/src/queue.rs`)

The core queue type (`storage/src/queue.rs:16`) is a linear `Vec<QueueEntry>` + a `head: usize` pointer +
a `capacity` + a BLAKE3 Merkle `root: [u8; 32]` + an optional boxed `WalState`.

- **State = the root.** "The queue root IS the content address of the queue state" (`queue.rs:5`). The
  root is recomputed over the *pending* slice `entries[head..]` (`recompute_root`, `queue.rs:357-365`) via
  the typed `commitment::blake3_binary_root` framework (`queue.rs:403-408`), with a typed Poseidon2 dual
  form computed-but-dropped at this boundary (`hash_entry`, `queue.rs:383-385`).
- **Enqueue = append leaf** (`queue.rs:264-273`): push entry, recompute root, reject if `is_full`
  (`len() >= capacity`, `queue.rs:317`).
- **Dequeue = advance head + emit a `DequeueProof`** (`queue.rs:276-295`): the proof carries
  `(entry, old_root, new_root, position)`.
- **HONEST PROTOTYPE FLAG IN THE RUST ITSELF.** `verify_dequeue_proof` (`queue.rs:416-426`) is **not a
  real Merkle-path verifier** — it only checks `old_root != new_root` (or the empty-queue edge). The Rust
  doc-comment admits: "A full implementation would verify Merkle paths; for Phase 1 we verify that the
  roots are different" (`queue.rs:414-415,419-420`). So even the Rust queue's dequeue soundness is a
  prototype; this is a place where "carry forward the Rust" means carrying forward an *acknowledged stub*,
  not a finished semantics.
- **QueueEntry** (`queue.rs:51-62`) carries `content_hash`, `sender`, `deposit` (computrons), `enqueued_at`
  (block height), `size`. The `deposit` and `sender` are the **deposit-accounting / refund** substrate the
  cell-program `total_deposits_held` slot tracks.

### 1.2 Write-Ahead Log — durable recovery (`storage/src/wal.rs`)

This is the real durability mechanism for `MerkleQueue` (`with_wal`, `enqueue_durable`, `dequeue_durable`,
`recover_from_wal`, `checkpoint`).

- **Log-before-apply discipline** (`queue.rs:148-155`, `queue.rs:177-185`): the WAL entry is `append`ed and
  `sync`ed (`writer.flush()` + `sync_all()`, `wal.rs:214-221`) **before** the in-memory mutation. This is
  the genuine WAL invariant.
- **Torn-write detection via per-line BLAKE3 checksum** (`wal.rs:106-108` serialize, `wal.rs:119-124`
  deserialize → `None` on checksum mismatch). Recovery skips corrupt lines silently (`wal.rs:296-299`),
  proven by the `wal_torn_write_recovery` test (`wal.rs:459-492`).
- **Replay reconstructs state** (`recover_from_wal`, `queue.rs:199-248`): fold `CreateQueue`/`Enqueue`/
  `Dequeue`/`Checkpoint` entries to rebuild `entries`+`head`.
- **Checkpoint + truncation** (`checkpoint`, `queue.rs:251-261`; `truncate_before`, `wal.rs:231-262`):
  write a `Checkpoint` entry, then rewrite the file keeping only `sequence >= seq` — space reclamation.
- **Sequence monotonicity** derived from the last entry on `open` (`wal.rs:182-189`).

### 1.3 Quota / computron metering — bounded execution (`storage/src/quota.rs`, `storage/src/metering.rs`)

- **`QuotaCell`** (`quota.rs:14-26`): `total_allocated`, `total_consumed`, `bytes_stored`, optional
  `max_bytes` hard cap. `charge` rejects with `QuotaExhausted` when `available() < cost`
  (`quota.rs:49-58`); `would_exceed_byte_cap` enforces the byte cap (`quota.rs:40-46`).
- **Rent, not buy** (`quota.rs:1-6`, `metering.rs:10-12`): `tick_epoch` (`quota.rs:200-212`) charges
  `bytes_stored * cost_per_byte` per epoch and returns the depleted quota ids → GC eligibility. This is the
  Robigalia "all resources owned and bounded" principle (`lib.rs:55-62`).
- **Refund-on-deletion** (`process_refund`, `quota.rs:161-175`; `refund_rate` default 0.8,
  `metering.rs:43`). Deletion is incentivized.
- **`MeteringPolicy::compute_cost`** (`metering.rs:48-99`) is the full storage-op cost table: `Write`,
  `Read`, `Splice`, `Delete`, `Relay` (TTL-priced, `metering.rs:66-68`), `Rental`, and the queue ops
  `Enqueue`/`Dequeue`/`CreateQueue`/`ResizeQueue`.

### 1.4 Erasure coding — data availability (`storage/src/erasure.rs`)

- **`ErasureEncoder`** (`erasure.rs:18-24`): `chunk_size` + `expansion_factor` (min 2). Encode → `n_data`
  data chunks + `n_data * (factor-1)` parity chunks (`erasure.rs:61-115`).
- **HONEST PROTOTYPE FLAG.** "This is a simplified prototype using XOR-based coding (not full
  Reed-Solomon)" (`erasure.rs:11-12`). `reconstruct` (`erasure.rs:120-193`) handles all-data-present and
  exactly-one-missing-chunk via XOR; general RS recovery is a stub (`erasure.rs:127-129`).
- **Availability sampling** (`sample_availability`, `erasure.rs:240-265`): `1 - (1/2)^K` confidence model
  for light-client chunk sampling — the trust model in `lib.rs:27-51` (OPERATOR-TRUSTED, bond-slashing
  dispute path).

### 1.5 The capability-secure VFS — Volume / Blob / Directory (`rbg/src/vfs.rs`)

This is the Robigalia VFS mapped onto dregg effects (`vfs.rs:1-35`):
- **Volume** = computron budget; `allocate`/`free` with overflow/underflow checks + nonce bump
  (`vfs.rs:209-235`); maps to the Effect VM balance-continuity row.
- **Blob** = content-addressed note (nameless write, Zhang et al.): `create` = `NoteCreate`, `delete` =
  `NoteSpend`, **`splice` = spend-old + create-new in one atomic turn** (`vfs.rs:328-388`,
  `VfsEffect::SpendBlob` + `CreateBlob` in one `EffectTrace`).
- **Directory** = c-list + factory provenance; **`swap` is the fundamental compare-and-swap primitive**
  (version = cell nonce, `vfs.rs:559-588`); `rename` = clear+set in one trace (`vfs.rs:614-647`).
- **Distributed GC** (`BlobRefTracker`, `vfs.rs:711-752`): a blob is collectible when ref-count hits zero
  across all directories AND the CapTP `ExportGcManager` count is zero.
- Each VFS op decomposes into existing Effect-VM rows (`VfsAirConstraints`, `vfs.rs:912-941`): "No new AIR
  is needed -- VFS is a user-space library on top of the existing proving system" (`vfs.rs:33-35`). This is
  itself the storage-as-cell-programs thesis stated for the VFS.

### 1.6 The REAL durable store — `persist/` (redb, crash-safe, the production tier)

This is the crate the Lean `CellRuntime` *should* be modeling and isn't.
- **redb-backed ACID KV with its own WAL** (`persist/src/lib.rs:13-15,148-151`): "crash-safe through
  redb's write-ahead logging." All mutations are `begin_write()` → `commit()` transactions.
- **Atomic note-spend** (`spend_note_atomic`, `lib.rs:625-661`): nullifier-insert + commitment-store in ONE
  transaction, double-spend rejected (`lib.rs:635-638`) — the real anti-double-spend, with TOCTOU races
  closed under the write lock (`note_tree_root`, `lib.rs:347-410`).
- **Recovery** (`recover_federation_state`, `recovery.rs:36-52`; `check_integrity` verifies chain
  continuity, `recovery.rs:61-80`).
- **Checkpoint + pruning** (`checkpoint.rs:33-54` store; `PruneResult` deletes roots/audit below the
  checkpoint height, opt-in for archival nodes, `checkpoint.rs:5-9`).
- **Proof-hash nullifier TTL pruning** for conditional-turn replay prevention (`lib.rs:528-589`).

---

## 2. The storage-as-cell-programs layer (the migration — Rust ground truth)

`dregg-storage-templates/` is the canonical realization of `STORAGE-AS-CELL-PROGRAMS.md`. The thesis
(`storage/src/lib.rs:1-25`, `STORAGE-AS-CELL-PROGRAMS.md:10-26`): the operator-side primitives in
`storage::{inbox,pubsub,blinded,programmable,operator,relay}` are **`#[deprecated]`** in favor of
cell-program templates; the **data structures** (`MerkleQueue`, `commitment`, `wal`) stay, only the
"parallel enforcement loop" is retired (`lib.rs:20-25`).

**Each template is a `FactoryDescriptor` + a `CellProgram::Cases` + turn-builders of existing effects.**
Confirmed in the Rust:
- `CapInbox` (`dregg-storage-templates/src/cap_inbox.rs`): 8 slots (`cap_inbox.rs:79-95`); program is
  `CellProgram::Cases([Always-invariants, send, dequeue, grant_sender])` (`cap_inbox.rs:150-263`) with
  `Immutable`/`MonotonicSequence`/`Monotonic`/`FieldLteField`/`SenderAuthorized` constraints; `send`/
  `dequeue`/`grant_sender` are built from **`Effect::SetField` + `Effect::EmitEvent` only**
  (`build_send_action`, `cap_inbox.rs:372-406`). No new effect. This IS a cell-program composing effects.
- `ProgrammableQueue` (`programmable_queue.rs`): constraint set **parameterized by the factory builder**
  (`programmable_queue_program_with`, `:217`), with caller-supplied `RateLimit`/`TemporalGate`/`Witnessed{Dfa}`
  (`:130`). The proof-of-pattern: same shape, richer menu.
- `PubSubTopic` (`pubsub_topic.rs`): append-only event log + subscriber cursors, monotone `event_root`.
- `BlindedQueue` (`blinded_queue.rs`): the **only** template carrying a `WitnessedPredicate::Custom { vk_hash }`
  (`blinded_queue.rs:67,128-129`) — the spend AIR; everything else is `Immutable`/`Monotonic`/`FieldLteField`/
  `MonotonicSequence`.
- `RelayOperator` (`relay_operator.rs`): economic cell-program — `BoundedBy` (bond decrement-on-dispute),
  `RateLimitBySum` (per-epoch byte quota), `SenderAuthorized`, `Witnessed{Dfa}` (`relay_operator.rs:18-50,
  193-219`); slash = `SetField` + `Transfer` (`:41`).

**The single enforcement loop.** All five route through the executor's `CellProgram::evaluate` over the
74-variant `StateConstraint` enum (`cell/src/program.rs:597`, which has `RateLimit`/`RateLimitBySum`/
`SenderAuthorized`/`WitnessedPredicate`/`TemporalGate`/`PreimageGate`/`BoundedBy` — `cell/src/program.rs:45,
161,307,489`). This is genuinely a DSL-userspace layer over the effect core.

**Two storage primitives are correctly NOT cell-programs** (`STORAGE-AS-CELL-PROGRAMS.md §4`):
`StorageMount` (a wire-level route-table decision, not a state machine) and `ContentStore` (kilobyte-to-
megabyte blobs that don't fit in 8×32-byte cell state; commitment-on-chain, bytes-off-chain).

---

## 3. LEAN-FIDELITY AUDIT (faithful / simplified-shadow / overlooked, file:line both sides)

Legend: **F** = faithful to Rust semantics; **S** = simplified-shadow (right shape, lossy); **O** =
overlooked/absent.

| Rust feature (file:line) | Lean module (file:line) | Verdict | Divergence flagged |
|---|---|---|---|
| **CapInbox as cell-program** (`cap_inbox.rs:150-263`: Cases send/dequeue/grant_sender, Immutable+MonotonicSequence+FieldLteField+SenderAuthorized) | `Exec/CapInbox.lean:77-93` `inboxProgram` (`predicate` of monotonic head/tail, immutable capacity/owner, `fieldLeField "tail" "head"`, `fieldLe "inflight" cap`) | **F (law) / S (shape)** | Lean is name-keyed 5-field record, NOT 8 slots (`CapInbox.lean:57-62`, deliberately per `dregg2 §5`); keystone `inbox_fifo` proves `tail ≤ head` + monotone cursors (`CapInbox.lean:200-236`) — the right law. |
| CapInbox **deposit accounting** `total_deposits_held` slot 6 (`cap_inbox.rs:90-92,300-306`); refund on dequeue | — | **O** | Lean inbox has NO `total_deposits`, NO `message_root`, NO `sender_set_root` fields; `inflight` derived register substitutes for capacity. Flagged honestly as `-- OPEN:` (`CapInbox.lean:85-92`). |
| CapInbox **message ring root** slot 7 + Merkle-membership dequeue (`cap_inbox.rs:93-95`) | — | **O** | No ring/Merkle model. Dequeue is a pure `tail += 1`. |
| CapInbox **SenderAuthorized** against `sender_set_root` (`cap_inbox.rs:199-203`) | `Exec/CapInbox.lean:273-302` `sendAuthorized`/`gatedSend` via `Caveat.Token` | **S** | Token-discharge gate is real & proved load-bearing (`send_requires_authorized_token`, `:294`); BUT the binding of token-subject to the on-wire sender / to `sender_set_root` is deferred `-- OPEN:` (`CapInbox.lean:318-325`) — exactly the authorization gap the migration was meant to CLOSE (`STORAGE-AS-CELL-PROGRAMS.md:51-60`). |
| **capacity bound** `head - tail ≤ capacity` (Rust: relational; doc §3.1 wants `FieldLteOther`) | `Exec/CapInbox.lean:84` derived `inflight` + `fieldLe` | **S** | The cross-slot relational variant is absent from both the Lean catalog and (per doc) the Rust 21-variant base; Lean honestly uses a derived register and flags the proper fix (`CapInbox.lean:85-92`). |
| **BlindedQueue** commitments-in/nullifiers-out, `countSpent ≤ countAdded`, Custom spend-AIR vk (`blinded_queue.rs:67,145-221`) | `Exec/BlindedQueue.lean` (commitments set, nullifier set, monotone counts) | **F (law) / S (crypto)** | Models the set/count law; the spend STARK is a deferred `Witnessed`/verify seam (same deferral pattern as CapInbox sender-binding). |
| **PubSubTopic** append-only `event_root`, subscriber cursors (`pubsub_topic.rs`) | `Exec/PubSubTopic.lean` | **F (law)** | Monotone event log + cursor law modeled; off-chain Merkle event delivery not modeled (correctly — it's out-of-band). |
| **RelayOperator** bond `BoundedBy`, `RateLimitBySum` quota, slash=`Transfer` (`relay_operator.rs:18-50`) | `Exec/RelayOperator.lean` | **F (economic law)** | Bond/quota/dispute economic invariants modeled; DFA dispatch is the `Witnessed{Dfa}` deferral. |
| **FactoryDescriptor** constructor transparency (`cell/src/factory.rs`; `cap_inbox.rs:272-356`) | `Exec/Factory.lean` | **F** | Models the EROS-style constructor + child-program-VK pinning (the delivery mechanism for the whole thesis). |
| **CellProgram** `Cases`/`Predicate` evaluation (`cell/src/program.rs:597`, 74 variants) | `Exec/Program.lean:55-100` `StateConstraint` (~16 variants) + `Exec/CellProgram.lean` | **S** | Lean catalog has fieldEq/Ge/Le/immutable/writeOnce/monotonic/strictMono/fieldDelta/not/fieldLeField/sumEquals/sumEqualsAcross/fieldDeltaInRange/allowedTransitions/anyOf/boundDelta. **MISSING from Lean: `RateLimit`, `RateLimitBySum`, `SenderAuthorized`, `WitnessedPredicate`, `TemporalGate`, `PreimageGate`, `BoundedBy`** (verified `Program.lean:20-23` defers Witnessed/sender/boundDelta to "dedicated passes"). The 74-vs-16 gap is the main constraint-vocabulary shadow. |
| **StateMigration** (schema upgrade reshape) | `Exec/StateMigration.lean:126-265` | **F (admirable)** | This is a *strong* faithful model: `applyMigration` is a fail-soft gate (commit reshape iff conforms-to-new-schema AND balance-preserved, else fall back to identity, `:131-132`); `migrate_conforms`/`migrate_conserves`/`migrate_anti_brick` proved (`:155,214,255`). Mirrors Mina's `fallback_to_signature_with_older_version`. Note: there is no *Rust* `StateMigration` equivalent yet — this is Lean **ahead of** the Rust (a vision to carry forward, not a fiction). |
| **MerkleQueue** linear buffer + BLAKE3 root + `recompute_root` (`queue.rs:16,357`) | — | **O** | No Merkle-queue data structure in Lean; the queue is modeled purely as head/tail integer cursors (`CapInbox.lean`). The content-addressed root semantics are absent. |
| **WAL** log-before-apply, fsync, torn-write checksum, replay, truncate (`wal.rs:106-299`) | `Exec/CellRuntime.lean:54-89` `checkpoint`/`restore`/`replayFrom` | **O (durability) / S (label)** | **This is the sharpest fiction risk.** `CellRuntime` names "checkpoint/restore/replay" but they are pure in-memory `Snapshot` round-trips: `checkpoint_restore_roundtrip` is `rfl` (`:60`), `restore (checkpoint s) = s` by definitional equality. There is NO fsync, NO torn-write recovery, NO log truncation, NO crash model. The Lean's "replay is deterministic" (`:79`) and "replay conserves the badge" (`:101`) are real *coalgebra* theorems but say nothing about the WAL's **durability** guarantee. The Rust durability (`wal.rs`, `persist/` redb) is the load-bearing semantics and the Lean does not touch it. |
| **Quota/computron metering**, byte caps, epoch rent, refund (`quota.rs`, `metering.rs`) | `Exec/Gas.lean` (gas accounting) — partial | **S/O** | A gas/cost model exists in Lean (`Gas.lean`) but does not model the storage-specific `bytes_stored`/`max_bytes`/`tick_epoch` rent-and-GC economics of `quota.rs:200-212`. The "storage is rented not bought + deletion refunds" economics are overlooked. |
| **Erasure coding** + availability sampling (`erasure.rs`) | — | **O** | Absent. (Arguably correctly out-of-scope for the kernel law — it's an availability/transport concern, like `ContentStore`.) |
| **VFS** Volume/Blob/Directory, splice-atomicity, dir-swap CAS, GC (`rbg/vfs.rs`) | partially via `Exec/NullifierCell.lean` (note spend/create) + `Exec/RecordCell` (CAS-shape) | **S/O** | The note-as-blob spend/create law has an analog (NullifierCell); the Directory CAS-by-nonce and BlobRefTracker GC are not modeled as VFS. |

---

## 4. The Rust semantics that MUST be carried forward faithfully (and where the Lean is a fiction/overlook)

Per the FID-ESCROW precedent — match the Rust kernel semantics, never a Lean simplification:

1. **The side-table / holding-store for the queue deposit (carry the Rust; the Lean overlooks it).**
   The Rust queue holds a `deposit` per entry (`queue.rs:57`), tracked in the cell-program's
   `total_deposits_held` slot (`cap_inbox.rs:90-92`), and refunds on dequeue. This is **structurally the
   same shape FID-ESCROW already modeled** for escrow: single-cell debit → side-table record → settle/
   refund (`turn/src/executor/apply.rs:1735,1770`; `EffectsPaired.lean:457-474,544-550`). The Lean
   `CapInbox` currently has NO deposit field at all. **Carry forward:** model the inbox deposit as the
   same holding-store register the escrow uses — conservation holds across send/dequeue *via the side
   register*, not per-effect. This is the one place the EFFECT-ISA-DESIGN's `C9 SideTable.lock` /
   `C10 SideTable.settle` (`EFFECT-ISA-DESIGN.md:249`) directly applies to storage.

2. **WAL durability is real semantics, not a tautology (carry the Rust; the Lean's `CellRuntime` is a
   label-fiction).** `CellRuntime.lean`'s checkpoint/restore is `rfl`-true of any record and conveys **no**
   durability content. The Rust guarantee — log-before-apply + fsync + torn-write checksum skip + replay +
   truncation (`wal.rs`), and redb ACID + atomic note-spend (`persist/lib.rs:625`) — is the actual "your
   data survives a crash, double-spends are rejected atomically" property. **Carry forward:** if the
   verified kernel is to *replace* the Rust, it must model a crash/recovery semantics (a log + a fault
   point + a replay-equals-pre-crash-state theorem), NOT rename a pure snapshot round-trip "checkpoint."
   The coalgebra replay-determinism theorems (`CellRuntime.lean:79,101`) are correct and worth keeping —
   but they are the *cache-rebuild* law, complementary to (not a substitute for) durability.

3. **The dequeue Merkle-proof and the SenderAuthorized→sender-set binding (the Rust is itself a stub here;
   carry forward the *finished* semantics, not either side's stub).** Both the Rust (`verify_dequeue_proof`
   is a roots-differ check, `queue.rs:416-426`, self-flagged Phase-1) and the Lean (sender-identity binding
   deferred, `CapInbox.lean:318-325`) leave the membership/identity binding incomplete. **Carry forward:**
   the finished semantics is a real Merkle-membership proof for dequeue + a real `sender_set_root` membership
   check for send — this is exactly what closes the authorization gap the migration exists to close
   (`STORAGE-AS-CELL-PROGRAMS.md:51-60`). Do NOT match the Rust's prototype `verify_dequeue_proof`; that
   would launder a known stub (the memory's "matching a buggy oracle launders the bug").

4. **The constraint vocabulary gap (carry the Rust 74-variant enum, not the Lean 16).** The Lean
   `StateConstraint` (`Program.lean:55-100`) lacks `RateLimit(BySum)`, `SenderAuthorized`, `WitnessedPredicate`,
   `TemporalGate`, `PreimageGate`, `BoundedBy` — precisely the variants `ProgrammableQueue`/`RelayOperator`/
   `BlindedQueue` need (`relay_operator.rs:193-219`, `blinded_queue.rs:67`). The Lean defers these to
   "dedicated passes" (`Program.lean:20-23`), which is honest but means the Lean cannot yet evaluate the
   richer templates. **Carry forward:** the law model must grow these (at least `RateLimitBySum`, `BoundedBy`,
   and the `Witnessed` discharge) to faithfully model `RelayOperator`/`BlindedQueue`.

---

## 5. The storage-as-cell-programs generalization × the effect-ISA basis

### 5.1 Is storage DSL-userspace over a small core, or does it need core primitives?

**Answer: it is overwhelmingly DSL-userspace over a small core, with exactly ONE core primitive the
templates genuinely need that the current ISA only half-expresses.**

The Rust proves the DSL-userspace thesis directly: every template operation is `SetField` + `EmitEvent`
(+ `Transfer` for deposit/slash) under a `CellProgram` (§2). No template defines a new `Effect`. The
EFFECT-ISA-DESIGN reached the same conclusion independently from the other side: "a queue is a *cell
program* (a CellProgram whose state field is a MerkleQueue), not a kernel primitive… everything
queue-specific is a userspace rule" (`EFFECT-ISA-DESIGN.md:178-180`), and the queue family
(`QueueAllocate/Resize/AtomicTx/PipelineStep`) is classified **DSL-USERSPACE / DERIVED-MACRO**, not CORE
(`EFFECT-ISA-DESIGN.md:276,421-428`). The five `Effect::Queue*` selectors (18–23) should *not* be kernel
selectors; the cell-program templates are the correct home.

**The one genuine core primitive the storage layer needs: the side-table/holding-store
(`C9 lock` / `C10 settle`).** This is NOT new — FID-ESCROW just added it to the kernel state
(`apply.rs:1735` `self.escrows`, modeled in `EffectsPaired.lean`'s holding-store). The point for storage:
the **queue deposit is the same holding-store** (debit sender → hold in a side register → refund on
dequeue). So storage does not need a *new* core effect beyond what escrow already forced into the kernel;
it needs the **same** holding-store, reused. The EFFECT-ISA-DESIGN already lists `C9/C10` as CORE
primitives that must stay in-circuit for one-trace atomicity (`EFFECT-ISA-DESIGN.md:249,365-368`). Storage
rides on them.

Everything else storage needs is already CORE-and-shared: `C6 Field.write` (= `SetField`, the slot
mutations), `C7 Meta.bind` (= `EmitEvent`, the event commitments), `C1 Balance.move` (= `Transfer`, deposit/
slash legs), `C13 Nonce.tick` (the directory-swap CAS version). The directory-`swap` CAS is `SetField` +
a nonce precondition (`vfs.rs:925-929`), i.e. `C6` + `C13` — not a new shape.

### 5.2 The right-basis fit

| storage primitive | reduces to (EFFECT-ISA CORE) | layer |
|---|---|---|
| MerkleQueue enqueue/dequeue | `C6 Field.write` (root advance) + `C9/C10` (deposit hold/refund) | DSL-userspace cell-program over CORE |
| CapInbox send/dequeue/grant | `C6` + `C7 Meta.bind` (event) + `C9/C10` (deposit) | DSL-userspace (template) |
| BlindedQueue add/consume | `C11 NoteTree.insert` / `C12 Nullifier.spend` + a `Custom` Witnessed | DSL-userspace + crypto-portal obligation |
| RelayOperator bond/slash/relay | `C1 Balance.move` + `C6` + `BoundedBy`/`RateLimitBySum` constraints | DSL-userspace (economic cell-program) |
| VFS blob splice | `C12` (spend old) + `C11` (create new) in one trace | DSL-userspace over CORE (atomic turn) |
| VFS directory swap (CAS) | `C6 Field.write` + `C13 Nonce.tick` | DSL-userspace |
| WAL durability, erasure, content store | — (NOT effects; transport/availability/host tier) | infrastructure, not ISA |
| Schema migration | `C6`-shaped reshape under a conformance+conservation gate | a kernel **upgrade** law (StateMigration.lean) |

**Conclusion on the generalization.** The Rust **supports the thesis cleanly**: storage is DSL-userspace
over a small effect core. The CapInbox/PubSubTopic/RelayOperator templates are genuinely
cell-programs-composing-effects, not bespoke. The **one** core primitive they require —
side-table/holding-store for the deposit — is already in the kernel (FID-ESCROW). The remaining
load-bearing Rust semantics (WAL durability, redb crash-safety, real Merkle dequeue proofs) are
**infrastructure below the ISA**, and the Lean's job there is not to rename them away (the `CellRuntime`
fiction) but to model the crash/recovery contract honestly if the kernel is to replace the Rust.

---

## 6. Honest non-claims (what this audit did NOT verify)

- I did not run `lake build` on the Lean modules; the "PROVED" labels and `#assert_axioms` lines are read
  off the source (`CapInbox.lean:282-289`, `StateMigration.lean:282-289`, `CellRuntime.lean:284-294`),
  not independently re-checked. They are *claimed* axiom-clean.
- I read the five `dregg-storage-templates` source files and `cap_inbox.rs` in full; `programmable_queue`/
  `relay_operator`/`blinded_queue`/`pubsub_topic` were read via targeted grep of their program/constraint/
  effect structure, not line-by-line.
- The Lean `Gas.lean` storage-economics fidelity (§3 row) is inferred from the module name + the absence of
  `bytes_stored`/`tick_epoch` mentions; I did not read `Gas.lean` in full.
- `STORAGE-AS-CELL-PROGRAMS.md` lives in `docs-old/` (archived); its design is nonetheless the one the
  current `dregg-storage-templates/` crate implements (the crate's own module docs cite it as canonical,
  `lib.rs:5-8,73`), so it is treated as the live thesis.

---

*A closing couplet, for the egg that stores its own warmth:*
*the queue is a cell, the cell is a law — / the deposit a side-note the escrow once saw;*
*but the log on the disk, the fsync, the recovery from crash — / is the Rust the proof must not paper as `rfl`-flash.* 🥚🐉
