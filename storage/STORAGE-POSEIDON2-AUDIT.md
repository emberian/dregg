# Storage Crate — Poseidon2 Migration Audit (P4.A)

**Author:** P4 (Stage 10 agent)
**Date:** 2026-05-24
**Scope:** every commitment construction site in `storage/src/`.
**Companion design:** `DESIGN-commitment-framework.md`, EFFECT-VM-SHAPE-A.md §S-1.

The Effect-VM-Shape-A master plan identifies Stage 10 ("Storage Poseidon2
migration") as a follow-on to Stage 1's typed `Commitment<T>` framework. The
self-admitted TODO at `storage/src/blinded.rs:329` ("would use Poseidon2 in
a real system") is the headline issue, but the storage crate contains
**many** other ad-hoc BLAKE3-only commitments that should funnel through a
typed `Commitment<T>` form to (a) get domain separation, (b) gain a
field-domain (Poseidon2) form when used as an Effect VM PI, and (c) lift
the type-level guarantees that the upstream `commit::typed` framework
already provides for cell/note/receipt commitments.

This audit enumerates every site, classifies it by intended migration
target, and proposes a per-site fix. The migration itself is split across
P4.C–P4.D.

---

## Cross-cutting observations

1. **Workspace exclusion.** `storage/` is in the `exclude` list of the root
   `Cargo.toml` (not `members`). This is significant for the migration:
   the upstream `commit/src/typed.rs` framework cannot be depended on
   without pulling the entire workspace's `pyana-dsl-runtime`. P4.B will
   take option (i) — a local `commitment.rs` module in `storage/src/`
   built atop `pyana_circuit::poseidon2`.
2. **Domain separation is informal.** Most sites use a literal byte-string
   tag (`b"blinded-queue-commitment"`, `b"queue_program_vk_v1"`, etc.)
   absorbed into a `blake3::Hasher`. There is no central registry. The
   typed framework's `domain` module is the right home — we'll add a
   per-storage-site set of constants in `commitment.rs`.
3. **Empty-state sentinels via plain hashes of magic strings.** Six
   different files use `blake3::hash(b"empty_…")` as the "empty" root.
   These should become `Commitment::empty()` (zero-valued sentinel) once
   migrated, matching upstream practice.
4. **Two distinct categories of commitment.** Reading across files, every
   site falls into one of two shapes:
   - **Single-value commitments** (binding of a struct to a 32-byte hash):
     queue entries, blinded items, content blobs, VK hashes, transaction
     hashes, pipeline identities. Migration target: `Commitment<T>`
     (single felt) or `Commitment4<T>` (four felts, when used standalone
     for proofs).
   - **Merkle roots** (binding of a sequence of items to a 32-byte root):
     blinded queue root, MerkleQueue root, programmable authorized-set
     root, sharded combined root, erasure root. Migration target:
     `MerkleRoot<T>`.

---

## Inventory

### blinded.rs (the headline site)

| Site (line) | Commits to | Today | Target | Notes |
|---|---|---|---|---|
| `crypto::create_commitment` (331) | Blinded item (item_data + randomness) | `blake3("blinded-queue-commitment" \|\| item \|\| rand)` | `Commitment4<BlindedItemMarker>` | Per the docstring TODO at 329. Must be Poseidon2 to match the in-circuit `NoteSpendingAir` (see line 14 docs). |
| `crypto::derive_nullifier` (340) | Nullifier (commitment + secret + position) | `blake3("blinded-queue-nullifier" \|\| …)` | `Commitment4<BlindedNullifierMarker>` | Mirrors upstream `cell::note::nullifier` shape. |
| `BlindedQueue::new` / empty root (123, 212, 377) | "empty queue" sentinel | `blake3(b"empty_blinded_queue")` | `MerkleRoot<BlindedItemSetMarker>::empty()` | |
| `merkle_root_of` (375) | Set of blinded commitments | BLAKE3 binary Merkle, zero-padded | `MerkleRoot<BlindedItemSetMarker>` (both BLAKE3 and Poseidon2 roots) | Internal use; the AIR side wants the Poseidon2 root. |
| `generate_merkle_proof` (404) | (proof generation) | BLAKE3 sibling path | needs Poseidon2 sibling path too | Currently dead code but kept for the test helper. |
| `verify_merkle_proof` (438) | (verification) | BLAKE3 recompute | needs Poseidon2 verify too | |

**Total: 4 commitment-producing sites + 2 verifier helpers.** The
migration target uses both BLAKE3 (for HashSet keys, gossip dedup) and
Poseidon2 (for AIR membership proofs).

### queue.rs

| Site (line) | Commits to | Today | Target |
|---|---|---|---|
| `recompute_root` (354–356) | "empty queue" sentinel | `blake3(b"empty_queue")` | `MerkleRoot<QueueEntrySetMarker>::empty()` |
| `hash_entry` (367) | A single `QueueEntry` (content+sender+deposit+enqueued_at+size) | `blake3` flat hash | `Commitment<QueueEntryMarker>` |
| `merkle_root` (381, 397) | Set of entry leaves | BLAKE3 binary Merkle | `MerkleRoot<QueueEntrySetMarker>` |
| `with_wal`/queue_id (98, 197) | Queue identity from WAL path | `blake3(path_bytes)` | leave as bare BLAKE3; this is an opaque identifier, not an authority-bearing commitment |

The "queue_id from WAL path" hashes are NOT authority-bearing — they're
opaque content-addressed identifiers used as `HashMap` keys. They stay
bare BLAKE3 per DESIGN-commitment-framework §3.4.

**Per-entry hash + Merkle root + empty sentinel = 3 distinct commitment
shapes.**

### programmable.rs

| Site (line) | Commits to | Today | Target |
|---|---|---|---|
| `compute_vk_hash` (604) | A queue program (name + constraints + lookup tables) | `blake3("queue_program_vk_v1" \|\| …)` | `Commitment<QueueProgramMarker>` |
| `hash_constraint` (634) | A single constraint (sub-hasher) | inline tag-prefixed `blake3` | folded into `QueueProgramMarker`'s `to_felts` |
| `compute_authorized_set_root` (679) | "empty authorized set" sentinel | `blake3(b"empty_authorized_set")` | `MerkleRoot<AuthorizedKeySetMarker>::empty()` |
| `compute_authorized_set_root` (683) | Singleton set | `blake3(key)` | `MerkleRoot<AuthorizedKeySetMarker>::singleton` |
| `compute_authorized_set_root` (688+) | Many-key Merkle | BLAKE3 binary Merkle | `MerkleRoot<AuthorizedKeySetMarker>` |
| `PreimageGate` verify (561) | Hashes a preimage to compare against commitment | `blake3(&preimage)` | matches the producer's commitment scheme; whichever the gate-creator chose |

The `PreimageGate` is an interesting edge case: it's a generic preimage
check where the commitment shape is fixed by the *caller* (whoever
created the gate). If the gate's `commitment` is a `Commitment<T>::blake3`
field, then BLAKE3 preimage check is correct. We leave the existing
BLAKE3 check in place and document that the gate is the BLAKE3 form of
whatever commitment the producer constructed.

**Compute_vk_hash + authorized_set_root = 2 commitment-producing
patterns, 1 unchanged verifier.**

### sharding.rs

| Site (line) | Commits to | Today | Target |
|---|---|---|---|
| `compute_combined_root` (170) | Concatenation of N shard roots | `blake3("sharded_queue_v1" \|\| roots…)` | `Commitment<ShardSetMarker>` (the combined root is a single binding over all shards; not itself a tree) |

**1 commitment site.**

### dataflow.rs

| Site (line) | Commits to | Today | Target |
|---|---|---|---|
| `compute_pipeline_id` (289) | A pipeline's full spec (stages, predicates, transforms) | `blake3("pipeline_v1" \|\| …)` | `Commitment<PipelineSpecMarker>` |
| `hash_predicate` (337) | Sub-hasher for predicates | inline `blake3` | folds into `PipelineSpecMarker::to_felts` |
| `TransformFn::Tag` re-hash (278) | Re-tag a content_hash via `blake3(old \|\| tag)` | `blake3` | leave bare; this is data-transformation, not a commitment |

**1 commitment site (with one sub-hasher).**

### atomic.rs

| Site (line) | Commits to | Today | Target |
|---|---|---|---|
| `tx_hash` (230) | A `QueueTransaction` (sequence of ops) | `blake3("queue_tx_v1" \|\| ops…)` | `Commitment<QueueTransactionMarker>` |

**1 commitment site.** The doc-comment says "for Effect VM binding" — so
this is a prime candidate for needing a Poseidon2 form (the Effect VM
absorbs PIs as BabyBear).

### erasure.rs

| Site (line) | Commits to | Today | Target |
|---|---|---|---|
| `encode` data-chunk commitment (79) | A chunk's data | `blake3(chunk_data)` | `Commitment<ErasureChunkMarker>` |
| `encode` parity commitment (104) | A parity chunk's data | `blake3(parity)` | `Commitment<ErasureChunkMarker>` (same marker, same shape) |
| `verify_chunk` (199) | Recompute & compare | BLAKE3 recompute | matches above |
| `root_commitment` (205) | Concatenation of all chunk commitments | `blake3` flat over commitments | `Commitment<ErasureSetMarker>` (flat, not tree — current code is a flat concatenation, not a Merkle tree) |

**3 commitment-producing sites + 1 verifier.** Per the file's own
"prototype" note, the underlying XOR coding is also placeholder; the
commitment migration should not block on the coding fix.

### content.rs

| Site (line) | Commits to | Today | Target |
|---|---|---|---|
| `ContentStore::hash` (47) | A blob | `blake3(data)` | leave as bare BLAKE3 |

Content-addressed storage IS BLAKE3 — there's no authority-bearing
commitment here, just a content key. The trait obligation is "anyone can
recompute and verify the bytes." No Poseidon2 form is needed. **Not
migrated.**

### multi_asset.rs

| Site (line) | Commits to | Today | Target |
|---|---|---|---|
| `usdc_asset` / `eth_asset` (225, 229) | Asset identifiers (test fixtures) | `blake3(b"USDC")` etc | test-only; **not migrated** |

### namespace_mount.rs

| Site (line) | Commits to | Today | Target |
|---|---|---|---|
| `mirrored_queue_verify_root` (368) | Test fixture (sets a root) | `blake3(b"queue state")` | test-only; **not migrated** |

### wal.rs

| Site (line) | Commits to | Today | Target |
|---|---|---|---|
| WAL frame checksum (106, 120) | Torn-write detection | `blake3(payload)` | leave bare; this is a fast file-integrity checksum, not a commitment |

WAL checksums are I/O-layer integrity, not authority-bearing. **Not
migrated.**

### poly_queue.rs

Behind the `kzg` feature; uses BLAKE3 → field-element reduction (line
675) as part of a polynomial commitment transcript. **Outside this
migration's scope** — KZG commitments are an orthogonal cryptosystem.

### pubsub.rs, operator.rs

`blake3` calls in these files are test-fixtures or BLAKE3 of bytes that
are explicitly content hashes (already in the bare-BLAKE3 category).
**Not migrated.**

---

## Migration target summary

After P4.B introduces the local typed framework, the following will exist
in `storage/src/commitment.rs`:

| Type | Used for | Cardinality of new sites |
|---|---|---|
| `Commitment<QueueEntryMarker>` | One per `QueueEntry` leaf | queue.rs |
| `MerkleRoot<QueueEntrySetMarker>` | Root of a `MerkleQueue` | queue.rs, sharding.rs |
| `Commitment4<BlindedItemMarker>` | One per blinded item | blinded.rs |
| `Commitment4<BlindedNullifierMarker>` | One per nullifier | blinded.rs |
| `MerkleRoot<BlindedItemSetMarker>` | BlindedQueue root | blinded.rs |
| `Commitment<QueueProgramMarker>` | VK hash | programmable.rs |
| `MerkleRoot<AuthorizedKeySetMarker>` | Authorized set | programmable.rs |
| `Commitment<ShardSetMarker>` | Combined sharded root | sharding.rs |
| `Commitment<PipelineSpecMarker>` | Pipeline identity | dataflow.rs |
| `Commitment<QueueTransactionMarker>` | Atomic-tx hash | atomic.rs |
| `Commitment<ErasureChunkMarker>` | One per chunk | erasure.rs |
| `Commitment<ErasureSetMarker>` | Combined erasure root | erasure.rs |

**Total new typed markers: 12.**
**Total commitment-producing sites migrated: 16** (across 7 production
files).
**Sites explicitly left as bare BLAKE3:** WAL checksums, content-address
hashes, opaque identifiers (queue_id from path), test fixtures, KZG
transcripts.

---

## Notes on the Poseidon2 source

The `pyana-circuit` crate is **already a viable upstream**:

- `pyana_circuit::field::BabyBear` is `pub`.
- `pyana_circuit::poseidon2::hash_4_to_1(&[BabyBear; 4]) -> BabyBear` is
  `pub` (line 341 of `circuit/src/poseidon2.rs`).
- `pyana_circuit::poseidon2::hash_many(&[BabyBear]) -> BabyBear` is `pub`
  (line 369).
- `pyana_circuit::field::BABYBEAR_P: u32` is `pub`.

This means P4.B can add `pyana-circuit = { path = "../circuit" }` to
`storage/Cargo.toml` as a normal path dependency **without widening any
visibility upstream**. No `pub use` re-exports are needed; the existing
Poseidon2 API at `pyana_circuit::poseidon2::*` is already public.

This also means P4.B's local `commitment.rs` module can be a direct
adaptation of `commit/src/typed.rs` (same domain-tagging strategy, same
`canonical_32_to_felts_4` shape) without copying any Poseidon2 round
constants or implementation details — those stay encapsulated in the
`circuit` crate.

---

## Out-of-scope (deferred)

- **In-circuit verification** of the migrated commitments. The Effect VM
  AIR additions for storage are Stage 7+ work (sovereign cell programs
  that prove "I dequeued from queue Q at root R"). This audit only
  migrates the producer side; the consumer side (AIR) will absorb the
  Poseidon2 form when those AIRs land.
- **KZG / poly_queue.rs.** Orthogonal cryptosystem (under `kzg`
  feature flag); no Poseidon2 form is meaningful for polynomial
  commitments.
- **Migrating queue_id / content_hash identifiers.** Bare BLAKE3 is
  correct for these: they're opaque content keys, not authority
  commitments. Migrating them would impose unnecessary cost.
- **Storage Stage 1 (sharding + dataflow) circuit forms.** The pipeline
  and shard commitments gain a Poseidon2 form here but no AIR yet
  consumes them; this lays groundwork for future circuit work.

---

## P4.C–P4.E plan

- **P4.C** — migrate `storage/src/blinded.rs` (headline site, 4
  producer sites + 2 verifiers). All `crypto::create_commitment` /
  `crypto::derive_nullifier` callers gain typed return values; the
  Merkle helpers go dual-form. Tests are updated to assert against the
  new typed shapes (which include both `blake3:` and `poseidon2:`
  fields).
- **P4.D** — migrate the remaining 6 production files
  (`queue.rs`, `programmable.rs`, `sharding.rs`, `dataflow.rs`,
  `atomic.rs`, `erasure.rs`). Each commitment site funnels through the
  typed framework.
- **P4.E** — add a stability unit test: hardcode the expected Poseidon2
  bytes for a known-input blinded-queue commitment so future
  algorithm drift is detectable.

End of audit.
