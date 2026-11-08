//! Table definitions for the redb database.
//!
//! Each table is defined as a constant with a fixed name and typed key/value pairs.
//! redb uses these definitions to enforce type safety at the database level.

use redb::TableDefinition;

/// Revocation set: token_id (string) -> revocation timestamp.
///
/// Key: token ID as a string (variable length).
/// Value: i64 timestamp when the revocation was recorded.
pub const REVOCATIONS: TableDefinition<&str, i64> = TableDefinition::new("revocations");

/// Attested roots: height (u64) -> serialized StoredAttestedRoot.
///
/// Key: block height (monotonically increasing).
/// Value: postcard-serialized `StoredAttestedRoot` struct.
pub const ATTESTED_ROOTS: TableDefinition<u64, &[u8]> = TableDefinition::new("attested_roots");

/// Metadata table for store-level counters and configuration.
///
/// Key: metadata key name.
/// Value: u64 value (used for counters like audit_sequence).
pub const METADATA: TableDefinition<&str, u64> = TableDefinition::new("metadata");

/// Re-genesis epoch of the canonical cell-state/ledger commitment schema.
/// Epoch 11 introduces the exact fields-root leaf and ledger-root v3.  A
/// missing marker is installable only on an authority-empty store; populated
/// unmarked/older stores are refused rather than silently reinterpreted.
pub const META_CANONICAL_STATE_SCHEMA_EPOCH: &str = "canonical_state_schema_epoch";

/// Note commitment tree: position (u64) -> 32-byte commitment hash.
///
/// Key: position in the append-only tree (0-based, monotonically increasing).
/// Value: 32-byte note commitment.
pub const NOTE_COMMITMENTS: TableDefinition<u64, &[u8; 32]> =
    TableDefinition::new("note_commitments");

/// Circuit-faithful note-commitment accumulator records.
///
/// Key: exact 32-byte commitment. Value: `value_le_u64 || seq_le_u64`.
/// The positional [`NOTE_COMMITMENTS`] table remains the public note-tree leaf
/// order; this additive table retains the value and append sequence required to
/// reconstruct `TurnExecutor::note_commitments` and its eight-felt root.
pub const NOTE_COMMITMENT_RECORDS_V1: TableDefinition<&[u8; 32], &[u8; 16]> =
    TableDefinition::new("note_commitment_records_v1");

/// Circuit-faithful revocation accumulator records.
///
/// Key: domain-separated revocation key. Value:
/// `revocation_height_le_u64 || seq_le_u64`.
pub const REVOCATION_RECORDS_V1: TableDefinition<&[u8; 32], &[u8; 16]> =
    TableDefinition::new("revocation_records_v1");

/// Restart-durable inbound bridge replay gate.
///
/// Key: source-federation note nullifier. Value: the commit ordinal which
/// first admitted it, retained so divergent-tail recovery can remove exactly
/// the rows introduced by truncated commits.
pub const BRIDGED_NULLIFIERS_V1: TableDefinition<&[u8; 32], u64> =
    TableDefinition::new("bridged_nullifiers_v1");

/// Restart-durable React replay gate.
///
/// Key: promise-hole nullifier in the React semantic domain. Value: the
/// finalized commit ordinal that first consumed it, allowing exact tail
/// rollback. These keys MUST NOT enter `NULLIFIERS`, whose sequence is the
/// proven faithful/exact-FNSP NoteSpend history.
pub const REACTIVE_NULLIFIERS_V1: TableDefinition<&[u8; 32], u64> =
    TableDefinition::new("reactive_nullifiers_v1");

/// Exact per-commit frontier for the dedicated React replay set.
pub const EXECUTOR_REACTIVE_NULLIFIER_FRONTIERS_V1: TableDefinition<u64, u64> =
    TableDefinition::new("executor_reactive_nullifier_frontiers_v1");

/// Post-turn accumulator frontier for every commit carrying executor side state.
///
/// Value: `commitment_count_le || revocation_count_le || bridged_count_le`.
/// These rows make replay exact and provide the rollback frontier for durable
/// tail recovery. They intentionally survive ordinary commit-log compaction.
pub const EXECUTOR_ACCUMULATOR_FRONTIERS_V1: TableDefinition<u64, &[u8; 24]> =
    TableDefinition::new("executor_accumulator_frontiers_v1");

/// Sparse canonical rate-limit snapshots keyed by commit ordinal.
///
/// A present row replaces the preceding snapshot. Absence means carry forward;
/// absence at ordinal zero means the canonical empty state. The persist crate
/// treats bytes opaquely so it remains independent of `dregg-turn`; the node
/// performs the strict versioned codec validation before capture and restore.
pub const EXECUTOR_RATE_LIMIT_SNAPSHOTS_V1: TableDefinition<u64, &[u8]> =
    TableDefinition::new("executor_rate_limit_snapshots_v1");

/// Sparse canonical factory-registry snapshots keyed by commit ordinal.
///
/// A present row replaces the preceding registry. Absence means carry forward;
/// absence at ordinal zero means the canonical empty registry. Unlike the
/// opaque rate snapshot, these bytes are strictly decoded and re-encoded by
/// `dregg-cell` at the persistence boundary before they can be committed.
pub const EXECUTOR_FACTORY_REGISTRY_SNAPSHOTS_V1: TableDefinition<u64, &[u8]> =
    TableDefinition::new("executor_factory_registry_snapshots_v1");

/// Canonical pending-turn registry successor at every executor-state commit.
///
/// Unlike sparse policy snapshots, every committed candidate carries an exact
/// successor. The writer verifies its expected predecessor commitment before
/// inserting this row; replay requires byte identity at the original ordinal.
pub const EXECUTOR_REACTIVE_REGISTRY_SNAPSHOTS_V1: TableDefinition<u64, &[u8]> =
    TableDefinition::new("executor_reactive_registry_snapshots_v1");

/// Post-finalization promise-resolution notifications.
///
/// This is an observer journal, not consensus authority: rows are appended in
/// the source finalized-turn transaction. The dense sequence is the resume
/// cursor served to game/bot clients.
pub const PROMISE_RESOLUTION_RECORDS_V1: TableDefinition<u64, &[u8]> =
    TableDefinition::new("promise_resolution_records_v1");

/// One canonical notification batch per source commit ordinal.
///
/// The manifest makes a replay byte-exact and prevents an interrupted caller
/// from extending or changing the event set for an already-published commit.
pub const PROMISE_RESOLUTION_BATCHES_V1: TableDefinition<u64, &[u8]> =
    TableDefinition::new("promise_resolution_batches_v1");

/// Current authenticated Path of Angels Signal head for each authority id.
///
/// The value is the strict, sealed `PoaSignalHeadV1` wire.  The authority id is
/// repeated inside the wire and checked on every load so a row cannot be moved
/// between keys without detection.
pub const POA_SIGNAL_HEADS_V1: TableDefinition<&[u8; 32], &[u8]> =
    TableDefinition::new("poa_signal_heads_v1");

/// Immutable Path of Angels Signal transition history.
///
/// Key: `authority_id || successor_transition_count_be`.  Values carry both
/// exact predecessor/successor heads and exact Lean judge input/output bytes.
pub const POA_SIGNAL_TRANSITIONS_V1: TableDefinition<&[u8; 40], &[u8]> =
    TableDefinition::new("poa_signal_transitions_v1");

/// Generic finalized commit ordinal -> exact PoA Signal transition key.
///
/// A generic commit can carry at most one Signal transition.  This reverse
/// index makes omission/invention on replay and divergent-tail rewind exact.
pub const POA_SIGNAL_BY_COMMIT_ORDINAL_V1: TableDefinition<u64, &[u8; 40]> =
    TableDefinition::new("poa_signal_by_commit_ordinal_v1");

/// Private AEAD-sealed dependent turns keyed by their promise/turn hash.
/// No value from this table is served by the public promise-resolution API.
pub const PRIVATE_DEPENDENT_TURNS_V1: TableDefinition<&[u8; 32], &[u8]> =
    TableDefinition::new("private_dependent_turns_v1");

/// Private, opaque ingress reservations created atomically with a dependent
/// turn's destructive Ready claim.  The key is a domain-separated digest of
/// the promise, Ready event, and signed-turn hash; values are never exposed by
/// the public PromiseResolution observer API.
pub const PRIVATE_DEPENDENT_INGRESS_RESERVATIONS_V1: TableDefinition<&[u8; 32], &[u8]> =
    TableDefinition::new("private_dependent_ingress_reservations_v1");

/// Versioned, hybrid-authenticated faithful-eight note-root transitions.
/// Key: finalized height. Value: strict `FaithfulNoteRootEnvelopeV1` bytes.
pub const FAITHFUL_NOTE_ROOT_HISTORY: TableDefinition<u64, &[u8]> =
    TableDefinition::new("faithful_note_root_history_v1");

/// Nullifier set: nullifier hash (32 bytes) -> unit (presence = spent).
///
/// Key: 32-byte nullifier hash.
/// Value: empty (presence in the table means the note is spent).
pub const NULLIFIERS: TableDefinition<&[u8; 32], ()> = TableDefinition::new("nullifiers");

/// Circuit-faithful nullifier accumulator records.
///
/// Key: the exact 32-byte revealed nullifier. Value: `value_le_u64 || seq_le_u64`.
/// The value is the public spent-note value consumed by the deployed grow-gate;
/// the sequence is the canonical finalized append rank.  Keeping this additive
/// record beside the legacy presence table lets restart reconstruct the same
/// eight-felt accumulator root instead of silently inventing values/order.
pub const NULLIFIER_RECORDS_V1: TableDefinition<&[u8; 32], &[u8; 16]> =
    TableDefinition::new("nullifier_records_v1");

/// Public-only authorities minted for faithfully finalized note spends.
///
/// Key: the exact public nullifier (globally one-shot). Value: the private
/// persist wire for [`crate::FinalizedFaithfulSpend`].  This table is written
/// only inside the finalized-turn weld, in the same redb transaction as the
/// nullifier record, receipt, commit record, faithful note-root edge, attested
/// root, and commit cursor.
pub const FINALIZED_FAITHFUL_SPENDS: TableDefinition<&[u8; 32], &[u8]> =
    TableDefinition::new("finalized_faithful_spends_v1");

/// Per-turn custody manifest for finalized faithful spends.
///
/// A row exists even when the turn finalized zero spends.  It pins the exact
/// ordered authority set, so an idempotent replay cannot omit a suffix (or the
/// entire set) and a loader can distinguish an honestly empty turn from a
/// truncated authority table.  The manifest survives commit-log compaction;
/// compacted loads additionally require the carrying block id in
/// [`COMMIT_COMPACTED_BLOCK_IDS`] and a covering finalized checkpoint.
pub const FINALIZED_FAITHFUL_SPEND_TURNS: TableDefinition<&[u8; 32], &[u8]> =
    TableDefinition::new("finalized_faithful_spend_turns_v1");

/// Checkpoints: height (u64) -> serialized Checkpoint.
///
/// Key: checkpoint height (always a multiple of the checkpoint interval).
/// Value: postcard-serialized `dregg_federation::Checkpoint` struct.
pub const CHECKPOINTS: TableDefinition<u64, &[u8]> = TableDefinition::new("checkpoints");

/// Byte-blob metadata table for values that don't fit in a u64.
///
/// Key: metadata key name.
/// Value: arbitrary byte blob (e.g., cached Merkle roots).
pub const METADATA_BYTES: TableDefinition<&str, &[u8]> = TableDefinition::new("metadata_bytes");

// Metadata key constants.

/// Key for the latest attested root height.
pub const META_LATEST_ROOT_HEIGHT: &str = "latest_root_height";

/// Key for the note tree size (number of commitments).
pub const META_NOTE_TREE_SIZE: &str = "note_tree_size";

/// Key for the cached note tree root (stored in METADATA_BYTES).
pub const META_NOTE_TREE_ROOT_CACHE: &str = "note_tree_root_cache";

/// Key for the cached Poseidon2 note tree root (stored in METADATA_BYTES).
///
/// Stored as 4 bytes (little-endian u32) representing the BabyBear field element.
/// Updated on every `store_note_commitment` / `spend_note_atomic` call.
pub const META_POSEIDON2_NOTE_TREE_ROOT_CACHE: &str = "poseidon2_note_tree_root_cache";

/// Fixed v1 history anchor (`FaithfulNoteRootAnchorV1`).
pub const META_FAITHFUL_NOTE_ROOT_ANCHOR: &str = "faithful_note_root_anchor_v1";

/// Transactionally updated exact count/head seal for truncation detection.
pub const META_FAITHFUL_NOTE_ROOT_HEAD: &str = "faithful_note_root_head_v1";

/// Quorum-signed version-2 statement binding exact prefix bytes and the mint
/// threshold plus ordered classical/PQ enrollment (`FaithfulNoteRootAuditSealV1`).
/// The key is unchanged; a policy-less version-1 value is ignored on load,
/// which authenticates rows without rewriting or migrating the database.
pub const META_FAITHFUL_NOTE_ROOT_AUDIT: &str = "faithful_note_root_audit_v1";

/// Key for the durable RECEIPT-INDEX HEAD anchor (stored in METADATA_BYTES).
///
/// The served `/api/receipts/index/*` non-omission MMR is projected from the
/// receipt chain; this compact `{ len: u64, root: [u8; 32] }` (40 bytes,
/// little-endian len ‖ root) is the last head the node served. On recovery the
/// rebuilt MMR is checked against it, so a receipt chain that no longer
/// reproduces the head served before restart is a detectable store-integrity
/// event (finding F5). It is a rebuildable cache — never commit-gating — and the
/// anchor that makes a future retention-windowed log compaction sound.
pub const META_RECEIPT_INDEX_HEAD: &str = "receipt_index_head_v1";

/// Key for the latest checkpoint height.
pub const META_LATEST_CHECKPOINT_HEIGHT: &str = "latest_checkpoint_height";

/// Ledger checkpoints: height (u64) -> serialized LedgerCheckpoint.
///
/// Key: block height at which the checkpoint was taken.
/// Value: postcard-serialized `LedgerCheckpoint` struct (full ledger state snapshot).
pub const LEDGER_CHECKPOINTS: TableDefinition<u64, &[u8]> =
    TableDefinition::new("ledger_checkpoints");

/// Key for the latest ledger checkpoint height.
pub const META_LATEST_LEDGER_CHECKPOINT_HEIGHT: &str = "latest_ledger_checkpoint_height";

// ─── Blocklace Tables ──────────────────────────────────────────────────────

/// Blocklace blocks: block_id (32 bytes) -> serialized Block.
///
/// Key: 32-byte block ID (blake3 hash of signed content + signature).
/// Value: postcard-serialized `Block` struct.
pub const BLOCKLACE_BLOCKS: TableDefinition<&[u8; 32], &[u8]> =
    TableDefinition::new("blocklace_blocks");

/// Blocklace metadata: key (string) -> arbitrary bytes.
///
/// Stores tips, equivocators, ordering state, and other blocklace metadata.
/// Key: metadata key name (e.g., "meta").
/// Value: postcard-serialized `BlocklaceMeta` struct.
pub const BLOCKLACE_META: TableDefinition<&str, &[u8]> = TableDefinition::new("blocklace_meta");

/// Key for the blocklace metadata blob in the BLOCKLACE_META table.
pub const BLOCKLACE_META_KEY: &str = "meta";

/// Key for the executed_up_to index in the BLOCKLACE_META table.
///
/// LEGACY/diagnostic: a bare COUNT of executed blocks. It is no longer a resume
/// point — an index into the tau order is unsound as a cursor because the order
/// can shift under honest catch-up growth (the machine-checked counterexample in
/// `metatheory/Dregg2/Consensus/TauPrefixMonotone.lean`). Recovery resumes from
/// the identity set (`BLOCKLACE_EXECUTED_IDS_KEY` ∪ the commit log's block ids).
pub const BLOCKLACE_EXECUTED_UP_TO_KEY: &str = "executed_up_to";

/// Key for the executed finalized-block IDENTITY set in the BLOCKLACE_META
/// table (postcard-serialized `Vec<BlockId>`, first-served order). Together
/// with the commit log's per-turn `block_id`s, this is the crash-consistent
/// resume state for the node's identity execution cursor (the TauPrefixMonotone
/// closure: execution tracked by block id, never by position).
pub const BLOCKLACE_EXECUTED_IDS_KEY: &str = "executed_block_ids";

/// Node-local witnessed receipt artifacts.
///
/// Key: receipt hash.
/// Value: caller-owned serialized witness vector. The persist crate keeps this
/// table byte-oriented so it does not depend on `dregg-turn`.
pub const WITNESSED_RECEIPTS: TableDefinition<&[u8; 32], &[u8]> =
    TableDefinition::new("witnessed_receipts");

/// Durable receipt chain — the node cipherclerk's per-turn `TurnReceipt` log, the
/// exact sequence `/api/receipts*` and the receipt-index MMR are served from.
///
/// Key: dense chain index (0-based ordinal, the receipt's position in the
/// cipherclerk chain). Value: caller-serialized `TurnReceipt` bytes. Byte-oriented
/// (like [`WITNESSED_RECEIPTS`]) so this crate stays independent of `dregg-turn`.
///
/// The in-memory `receipt_chain` used to be rebuilt EMPTY every boot, so
/// `/api/receipts/index/head` served `len = 0` after a restart even though the
/// ledger recovered. Persisting each appended receipt here — reloaded into the
/// cipherclerk on boot — makes the receipt chain + MMR head durable across a
/// restart, riding the same redb discipline as the ledger. Load requires the
/// complete dense sequence from index 0; any gap is an integrity error, never an
/// excuse to silently roll the accepted head back to a prefix.
pub const RECEIPT_CHAIN: TableDefinition<u64, &[u8]> = TableDefinition::new("receipt_chain");

/// Durable REALM-substrate turn/operation log — the ordered, hash-linked history
/// of admitted `realm-model` operations (`realm-model/`, the §9.4/§9.5/§9.2 MUD
/// substrate) the running node hosts via `dregg-node`'s `realm_service`.
///
/// Key: dense op index (0-based ordinal). Value: caller-serialized `RealmOp`
/// bytes (postcard). Byte-oriented (like [`RECEIPT_CHAIN`]) so this crate stays
/// independent of `realm-model`/`dregg-turn`.
///
/// This is the durable half of the dependency `docs/design/MUD-SUBSTRATE.md`
/// §"the receipt-chain dependency" named as not-built: a `RealmWorld` chains
/// realm receipts (`previous_receipt_hash`) in-memory only, so a realm's history
/// survives only while one process holds it. Replaying this dense log on boot
/// through a fresh `RealmWorld` reconstructs the identical realm/instance/identity
/// state AND the identical receipt-chain head — realm persistence across a node
/// restart, riding the exact density discipline of [`RECEIPT_CHAIN`]. Load
/// requires the complete dense sequence from index 0; any gap is an integrity
/// error, never an excuse to roll the accepted realm head back to a prefix.
pub const REALM_LOG: TableDefinition<u64, &[u8]> = TableDefinition::new("realm_log");

// ─── Durable Commit Log + Index (crash-consistency) ─────────────────────────
//
// The commit log is the authoritative, append-only record of finalized turns
// that THIS node has applied to its ledger. It is the recovery anchor: each
// record is written in the SAME redb transaction that advances the commit
// cursor (`META_COMMIT_CURSOR`), so the cursor and the per-turn record can
// never be torn against each other. The index tables below are secondary
// views derived from this log; every index write happens in that same
// transaction, so the "index entry exists iff the log has it" invariant holds
// by construction across crashes.

/// Commit log: commit ordinal (u64, 0-based, == position in the tau-finalized
/// order this node has applied) -> postcard-serialized `CommitRecord`.
///
/// Key: the commit ordinal (a dense, gap-free counter advanced by exactly one
/// per applied turn; equals the prior `executed_up_to` semantics but is now the
/// crash-consistent anchor written atomically with the record itself).
/// Value: postcard-serialized `commit_log::CommitRecord`.
pub const COMMIT_LOG: TableDefinition<u64, &[u8]> = TableDefinition::new("commit_log");

/// Index — receipt by hash: receipt_hash (32 bytes) -> commit ordinal (u64).
///
/// Lets a verifier/explorer resolve a receipt hash to its commit position in
/// O(1) without scanning. The pointed-to `CommitRecord` carries the full
/// coordinates (height, creator, turn hash, ledger root).
pub const IDX_RECEIPT_BY_HASH: TableDefinition<&[u8; 32], u64> =
    TableDefinition::new("idx_receipt_by_hash");

/// Index — turn by hash: turn_hash (32 bytes) -> commit ordinal (u64).
pub const IDX_TURN_BY_HASH: TableDefinition<&[u8; 32], u64> =
    TableDefinition::new("idx_turn_by_hash");

/// Index — turns by (height, creator): composite key -> commit ordinal (u64).
///
/// Key layout: 8-byte big-endian height ++ 32-byte creator ++ 8-byte
/// big-endian ordinal. Big-endian height makes redb's lexicographic range
/// scan equal a height-ordered scan, so "all turns at height H" and "all
/// turns by creator C in height order" are efficient range queries. The
/// trailing ordinal keeps keys unique when several turns commit at the same
/// `(height, creator)` — the normal case for ROUTE-level turns (the
/// trustline/court/channels services), several of which can commit between
/// two attested-height advances. Stores written with the older 40-byte key
/// are migrated by `migrate_height_creator_index` at open.
pub const IDX_TURN_BY_HEIGHT_CREATOR: TableDefinition<&[u8], u64> =
    TableDefinition::new("idx_turn_by_height_creator");

/// Index — cell by id (durable per-turn snapshot): cell_id (32 bytes) ->
/// postcard-serialized `dregg_cell::Cell`.
///
/// Updated atomically per applied turn from the executor's post-state so a
/// node can look up the current contents of ANY cell touched since the last
/// full ledger checkpoint, without replaying. Cells not touched since the last
/// checkpoint are served from the checkpoint; this table holds the deltas on
/// top of it. Rebuilt deterministically from the commit log on demand.
pub const IDX_CELL_BY_ID: TableDefinition<&[u8; 32], &[u8]> =
    TableDefinition::new("idx_cell_by_id");

/// Last per-cell generic receipt writer in the compacted commit-log prefix.
///
/// Key: cell id. Value: `writer_ordinal_le_u64 || receipt_hash_32`. A removed
/// cell deliberately retains a row: re-creating an id must extend, not erase,
/// its finalized provenance. This baseline is folded before the corresponding
/// commit records are deleted by compaction.
pub const PER_CELL_RECEIPT_HEAD_BASELINE_V1: TableDefinition<&[u8; 32], &[u8; 40]> =
    TableDefinition::new("per_cell_receipt_head_baseline_v1");

/// Last per-cell generic receipt writer over the complete applied history.
///
/// This is the bounded constructor index: `baseline` replayed with the dense
/// live suffix `[commit_compacted_floor, commit_cursor)`. It is updated in the
/// finalized-turn transaction and rebuilt from baseline + survivors on tail
/// recovery.
pub const PER_CELL_RECEIPT_HEAD_CURRENT_V1: TableDefinition<&[u8; 32], &[u8; 40]> =
    TableDefinition::new("per_cell_receipt_head_current_v1");

/// Key (in METADATA) for the durable commit cursor: the number of turns this
/// node has committed and indexed = the next free commit ordinal. This is the
/// crash-consistent replacement for the separately-written
/// `BLOCKLACE_EXECUTED_UP_TO_KEY`; recovery reads THIS value (advanced inside
/// the per-turn commit transaction) as the authoritative high-water mark.
pub const META_COMMIT_CURSOR: &str = "commit_cursor";

/// Key (in METADATA) for the durable commit-log COMPACTION FLOOR: the number of
/// commit records that have been compacted away (`compact_below`) because a
/// finalized ledger checkpoint at/above their height subsumes them. Equals the
/// lowest commit ordinal still physically present in [`COMMIT_LOG`]: every
/// ordinal in `[compacted_floor, commit_cursor)` resolves to a record; ordinals
/// in `[0, compacted_floor)` were compacted (their finalized state lives in the
/// checkpoint). 0 on a node that has never compacted. NEVER advances the cursor.
///
/// The post-compaction index-audit density invariant is
/// `commit_cursor() == commit_log.len() + compacted_floor` (the pre-compaction
/// `cursor == len` is the `compacted_floor == 0` special case).
pub const META_COMMIT_COMPACTED: &str = "commit_compacted_floor";

/// Installed schema marker for the two-map per-cell receipt-head index.
///
/// Absence can be migrated only while the compaction floor is zero. Once any
/// commit records have been compacted, their write sets no longer exist and an
/// absent baseline is unreconstructable, so open fails closed.
pub const META_PER_CELL_RECEIPT_HEAD_INDEX_VERSION_V1: &str =
    "per_cell_receipt_head_index_version_v1";

/// Compacted turn block-ids: the blocklace `block_id` of every turn whose commit
/// record was compacted away (presence = a turn this node DURABLY APPLIED whose
/// record is no longer in [`COMMIT_LOG`] because a checkpoint subsumes it).
///
/// This is load-bearing for **no-double-apply**: the node's identity execution
/// cursor (`node/src/execution_cursor.rs`) re-executes a turn block on recovery
/// iff its id is NOT among the durable applied-turn ids, and the persist-side
/// source of those ids is [`PersistentStore::commit_log_block_ids`]. Compacting
/// a record removes its id from the live commit log, so this set carries it
/// forward: `commit_log_block_ids` returns the SURVIVORS' ids ∪ this set, i.e.
/// the full set of applied-turn ids, unchanged by compaction. Without it, a
/// compacted (already-applied) turn would look un-executed and be re-applied on
/// top of the checkpoint that already includes it (a double-apply).
///
/// Key: 32-byte turn block id. Value: unit (presence = compacted-but-applied).
pub const COMMIT_COMPACTED_BLOCK_IDS: TableDefinition<&[u8; 32], ()> =
    TableDefinition::new("commit_compacted_block_ids");

// ─── Forever-Digest Sets (restart-durable anti-replay carriers) ──────────────
//
// Several node registries carry "burned forever" digest sets whose refusal
// semantics must survive a process restart: the trustline draw / rebuild /
// settle-unapplied digests (Lean `no_double_draw_forever`,
// `draw_replay_refused_across_epochs` — the slice's own debit list resets at
// every rebalance epoch, so the FOREVER property needs a carrier that does
// not) and the equivocation court's resolved-evidence digests (no-double-
// resolve / no-double-slash). These are NOT derivable from the cells: the
// cell holds only the LAST digest (`TL_DIGEST_SLOT`) and the court's verdicts
// move value without leaving the full digest set on any cell. See
// `.docs-history-noclaude/PERSISTENCE.md`.

/// Forever-burned digest sets, namespaced per registry and scoped per cell.
///
/// Key layout: 1-byte namespace ++ 32-byte scope ++ 32-byte digest = 65 bytes.
/// Value: unit (presence = burned).
///
/// The scope is the cell the digest was burned against (the trustline cell id
/// for `NS_TRUSTLINE_DIGEST`); namespaces whose digests are global use the
/// all-zero scope.
pub const FOREVER_DIGESTS: TableDefinition<&[u8; 65], ()> = TableDefinition::new("forever_digests");

/// Namespace byte: the node's trustline digest registry (committed draws,
/// shadow-rebuild digests, settle-unapplied compensation digests — everything
/// `TrustlineRegistry::record_digest` burns).
pub const NS_TRUSTLINE_DIGEST: u8 = 1;

/// Namespace byte: the equivocation court's resolved-evidence digests
/// (scope = all-zero; evidence digests are global, not per-cell).
pub const NS_COURT_RESOLVED: u8 = 2;

// ─── Durable Channel Rosters (.docs-history-noclaude/PERSISTENCE.md §3, the roster caveat) ─────
//
// The channel-group cell holds only the roster's COMMITMENT
// (`CH_MEMBER_ROOT_SLOT`); the member→seal-pk CONTENT is node-held and
// verifiable-but-not-derivable from the cell. This table is the durable
// carrier: written after every committed epoch step, re-committed against the
// on-cell root at load (a stale durable roster is DISCARDED, fail-closed —
// `RosterStale` then means genuine divergence, not a mere restart).

/// Channel rosters: channel cell id (32 bytes) -> postcard-serialized roster
/// (`BTreeMap<CellId, [u8; 32]>` — member cell → X25519 seal pk).
pub const CHANNEL_ROSTERS: TableDefinition<&[u8; 32], &[u8]> =
    TableDefinition::new("channel_rosters");
