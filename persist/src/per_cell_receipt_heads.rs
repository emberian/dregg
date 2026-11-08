//! Restart-durable per-cell receipt provenance.
//!
//! A live [`crate::CommitRecord`] carries the finalized receipt hash together
//! with its complete write set (`touched_cells` plus `removed`).  Replaying the
//! dense live suffix can therefore reconstruct each cell's latest generic-turn
//! provenance head.  Commit-log compaction destroys the write sets in the
//! compacted prefix, however, so one latest-head table is not enough: divergent
//! tail recovery may need to roll a cell back from a discarded live writer to a
//! predecessor whose commit record has already been compacted.
//!
//! The durable model is consequently two bounded maps:
//!
//! - `baseline`: last-writer-wins over compacted ordinals `[0, floor)`;
//! - `current`: `baseline` replayed with the dense live suffix
//!   `[floor, cursor)`.
//!
//! A removal advances provenance just like an upsert.  Re-creating the same cell
//! id must not make its history appear to start at genesis.

use std::collections::{BTreeMap, BTreeSet};

use dregg_cell::CellId;
use redb::{ReadTransaction, ReadableTable, ReadableTableMetadata, WriteTransaction};

use crate::commit_log::{CommitRecord, decode_commit_record};
use crate::{PersistentStore, Result, StoreError, tables};

/// Maximum number of distinct cell provenance heads in either durable map.
///
/// This is an integrity/resource boundary, not an eviction policy.  Crossing it
/// refuses the committing transaction; silently dropping an old head would make
/// a later re-created cell appear to have no predecessor.
pub const MAX_PER_CELL_RECEIPT_HEADS_V1: u64 = 1_000_000;

/// Maximum number of live commit records replayed at restart.
///
/// Ordinary checkpoint-driven compaction keeps this suffix bounded.  Refusing a
/// larger image is preferable to allocating from an attacker-controlled cursor.
pub const MAX_PER_CELL_RECEIPT_LIVE_RECORDS_V1: u64 = 1_000_000;

/// On-disk schema marker stored in [`tables::METADATA`].
pub const PER_CELL_RECEIPT_HEAD_INDEX_VERSION_V1: u64 = 1;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct DurablePerCellReceiptHead {
    pub cell: CellId,
    pub writer_ordinal: u64,
    pub receipt_hash: [u8; 32],
}

/// Complete, independently validated restart image.
///
/// `current` is included rather than trusted: the node replays `baseline` plus
/// `live_records` and requires byte-identical equality before installing any
/// executor state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PerCellReceiptHeadRecovery {
    pub compacted_floor: u64,
    pub cursor: u64,
    pub baseline: Vec<DurablePerCellReceiptHead>,
    pub current: Vec<DurablePerCellReceiptHead>,
    pub live_records: Vec<CommitRecord>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct HeadValue {
    writer_ordinal: u64,
    receipt_hash: [u8; 32],
}

fn integrity(message: impl Into<String>) -> StoreError {
    StoreError::Integrity(message.into())
}

fn bounded_len(count: u64, limit: u64, kind: &str) -> Result<usize> {
    if count > limit {
        return Err(integrity(format!(
            "{kind} count {count} exceeds durable bound {limit}"
        )));
    }
    usize::try_from(count).map_err(|_| integrity(format!("{kind} count does not fit usize")))
}

fn encode_head(head: HeadValue) -> [u8; 40] {
    let mut out = [0u8; 40];
    out[..8].copy_from_slice(&head.writer_ordinal.to_le_bytes());
    out[8..].copy_from_slice(&head.receipt_hash);
    out
}

fn decode_head(bytes: &[u8; 40]) -> HeadValue {
    let mut ordinal = [0u8; 8];
    ordinal.copy_from_slice(&bytes[..8]);
    let mut receipt_hash = [0u8; 32];
    receipt_hash.copy_from_slice(&bytes[8..]);
    HeadValue {
        writer_ordinal: u64::from_le_bytes(ordinal),
        receipt_hash,
    }
}

fn record_participants(record: &CommitRecord) -> Result<Vec<[u8; 32]>> {
    let count = record
        .touched_cells
        .len()
        .checked_add(record.removed.len())
        .ok_or_else(|| integrity("commit participant count overflow"))?;
    let count =
        u64::try_from(count).map_err(|_| integrity("commit participant count does not fit u64"))?;
    let capacity = bounded_len(
        count,
        MAX_PER_CELL_RECEIPT_HEADS_V1,
        "per-commit cell participant",
    )?;
    let mut participants = BTreeSet::new();
    for cell in &record.touched_cells {
        if !participants.insert(cell.id().0) {
            return Err(integrity(format!(
                "commit record {} names cell {:?} more than once across touched/removed",
                record.ordinal,
                cell.id()
            )));
        }
    }
    for cell in &record.removed {
        if !participants.insert(*cell) {
            return Err(integrity(format!(
                "commit record {} names cell {:?} more than once across touched/removed",
                record.ordinal,
                CellId(*cell)
            )));
        }
    }
    debug_assert_eq!(participants.len(), capacity);
    Ok(participants.into_iter().collect())
}

fn collect_heads(
    table: &impl ReadableTable<&'static [u8; 32], &'static [u8; 40]>,
    kind: &str,
) -> Result<BTreeMap<[u8; 32], HeadValue>> {
    let capacity = bounded_len(table.len()?, MAX_PER_CELL_RECEIPT_HEADS_V1, kind)?;
    let mut heads = BTreeMap::new();
    for entry in table.iter()? {
        let (cell, encoded) =
            entry.map_err(|error: redb::StorageError| StoreError::Database(error.to_string()))?;
        heads.insert(*cell.value(), decode_head(encoded.value()));
    }
    debug_assert_eq!(heads.len(), capacity);
    Ok(heads)
}

fn collect_live_records(
    log: &impl ReadableTable<u64, &'static [u8]>,
    compacted_floor: u64,
    cursor: u64,
) -> Result<Vec<CommitRecord>> {
    let count = cursor.checked_sub(compacted_floor).ok_or_else(|| {
        integrity(format!(
            "per-cell receipt-head cursor {cursor} is behind compaction floor {compacted_floor}"
        ))
    })?;
    let capacity = bounded_len(
        count,
        MAX_PER_CELL_RECEIPT_LIVE_RECORDS_V1,
        "live per-cell receipt-head commit suffix",
    )?;
    if log.len()? != count {
        return Err(integrity(format!(
            "live commit-log length {} disagrees with cursor({cursor}) - floor({compacted_floor}) = {count}",
            log.len()?
        )));
    }

    let mut records = Vec::with_capacity(capacity);
    for (index, entry) in log.iter()?.enumerate() {
        let (key, bytes) =
            entry.map_err(|error: redb::StorageError| StoreError::Database(error.to_string()))?;
        let index = u64::try_from(index)
            .map_err(|_| integrity("live commit-log index does not fit u64"))?;
        let expected = compacted_floor
            .checked_add(index)
            .ok_or_else(|| integrity("live commit-log ordinal overflow"))?;
        if key.value() != expected {
            return Err(integrity(format!(
                "live commit-log ordinal {} is not dense expected ordinal {expected}",
                key.value()
            )));
        }
        let record = decode_commit_record(bytes.value())?;
        if record.ordinal != expected {
            return Err(integrity(format!(
                "commit-log key {expected} carries record ordinal {}",
                record.ordinal
            )));
        }
        records.push(record);
    }
    Ok(records)
}

fn validate_baseline(compacted_floor: u64, baseline: &BTreeMap<[u8; 32], HeadValue>) -> Result<()> {
    if compacted_floor == 0 && !baseline.is_empty() {
        return Err(integrity(
            "per-cell receipt-head baseline is nonempty at compaction floor zero",
        ));
    }
    for (cell, head) in baseline {
        if head.writer_ordinal >= compacted_floor {
            return Err(integrity(format!(
                "per-cell receipt-head baseline for {:?} names writer {} outside compacted prefix [0, {compacted_floor})",
                CellId(*cell),
                head.writer_ordinal
            )));
        }
    }
    Ok(())
}

fn reconstruct_projection(
    compacted_floor: u64,
    cursor: u64,
    baseline: &BTreeMap<[u8; 32], HeadValue>,
    live_records: &[CommitRecord],
) -> Result<BTreeMap<[u8; 32], HeadValue>> {
    validate_baseline(compacted_floor, baseline)?;
    let expected_count = cursor.checked_sub(compacted_floor).ok_or_else(|| {
        integrity(format!(
            "per-cell receipt-head cursor {cursor} is behind compaction floor {compacted_floor}"
        ))
    })?;
    let expected_count = bounded_len(
        expected_count,
        MAX_PER_CELL_RECEIPT_LIVE_RECORDS_V1,
        "live per-cell receipt-head commit suffix",
    )?;
    if live_records.len() != expected_count {
        return Err(integrity(format!(
            "live per-cell receipt-head suffix [{compacted_floor}, {cursor}) has {} records, expected {expected_count}",
            live_records.len()
        )));
    }

    let mut projection = baseline.clone();
    for (index, record) in live_records.iter().enumerate() {
        let index = u64::try_from(index)
            .map_err(|_| integrity("live per-cell receipt-head index does not fit u64"))?;
        let expected = compacted_floor
            .checked_add(index)
            .ok_or_else(|| integrity("live per-cell receipt-head ordinal overflow"))?;
        if record.ordinal != expected {
            return Err(integrity(format!(
                "live per-cell receipt-head record ordinal {} is not dense expected ordinal {expected}",
                record.ordinal
            )));
        }
        let head = HeadValue {
            writer_ordinal: record.ordinal,
            receipt_hash: record.receipt_hash,
        };
        for cell in record_participants(record)? {
            projection.insert(cell, head);
        }
        bounded_len(
            u64::try_from(projection.len()).unwrap_or(u64::MAX),
            MAX_PER_CELL_RECEIPT_HEADS_V1,
            "current per-cell receipt-head",
        )?;
    }
    Ok(projection)
}

fn require_exact_projection(
    expected: &BTreeMap<[u8; 32], HeadValue>,
    current: &BTreeMap<[u8; 32], HeadValue>,
) -> Result<()> {
    if expected == current {
        return Ok(());
    }
    let first_difference = expected
        .keys()
        .chain(current.keys())
        .find(|cell| expected.get(*cell) != current.get(*cell))
        .copied();
    Err(integrity(match first_difference {
        Some(cell) => format!(
            "durable current per-cell receipt-head for {:?} disagrees with compacted baseline plus live suffix",
            CellId(cell)
        ),
        None => {
            "durable current per-cell receipt-head map disagrees with reconstruction".to_string()
        }
    }))
}

fn rows(heads: &BTreeMap<[u8; 32], HeadValue>) -> Vec<DurablePerCellReceiptHead> {
    heads
        .iter()
        .map(|(cell, head)| DurablePerCellReceiptHead {
            cell: CellId(*cell),
            writer_ordinal: head.writer_ordinal,
            receipt_hash: head.receipt_hash,
        })
        .collect()
}

fn clear_head_table(
    write: &WriteTransaction,
    definition: redb::TableDefinition<&'static [u8; 32], &'static [u8; 40]>,
) -> Result<()> {
    let mut table = write.open_table(definition)?;
    let keys: Vec<[u8; 32]> = table
        .iter()?
        .filter_map(|entry| entry.ok().map(|entry| *entry.0.value()))
        .collect();
    for key in keys {
        table.remove(&key)?;
    }
    Ok(())
}

fn install_current(
    write: &WriteTransaction,
    current: &BTreeMap<[u8; 32], HeadValue>,
) -> Result<()> {
    bounded_len(
        u64::try_from(current.len()).unwrap_or(u64::MAX),
        MAX_PER_CELL_RECEIPT_HEADS_V1,
        "current per-cell receipt-head",
    )?;
    clear_head_table(write, tables::PER_CELL_RECEIPT_HEAD_CURRENT_V1)?;
    let mut table = write.open_table(tables::PER_CELL_RECEIPT_HEAD_CURRENT_V1)?;
    for (cell, head) in current {
        let encoded = encode_head(*head);
        table.insert(cell, &encoded)?;
    }
    Ok(())
}

/// `(index version, compaction floor, commit cursor)` as of `read`.
fn index_meta(read: &ReadTransaction) -> Result<(Option<u64>, u64, u64)> {
    let meta = read.open_table(tables::METADATA)?;
    Ok((
        meta.get(tables::META_PER_CELL_RECEIPT_HEAD_INDEX_VERSION_V1)?
            .map(|value| value.value()),
        meta.get(tables::META_COMMIT_COMPACTED)?
            .map(|value| value.value())
            .unwrap_or(0),
        meta.get(tables::META_COMMIT_CURSOR)?
            .map(|value| value.value())
            .unwrap_or(0),
    ))
}

fn projection_from_read(
    read: &ReadTransaction,
) -> Result<(
    u64,
    u64,
    BTreeMap<[u8; 32], HeadValue>,
    BTreeMap<[u8; 32], HeadValue>,
    Vec<CommitRecord>,
)> {
    let (version, compacted_floor, cursor) = index_meta(read)?;
    if version != Some(PER_CELL_RECEIPT_HEAD_INDEX_VERSION_V1) {
        return Err(integrity(format!(
            "per-cell receipt-head index version is {:?}, expected {}",
            version, PER_CELL_RECEIPT_HEAD_INDEX_VERSION_V1
        )));
    }
    let baseline = collect_heads(
        &read.open_table(tables::PER_CELL_RECEIPT_HEAD_BASELINE_V1)?,
        "baseline per-cell receipt-head",
    )?;
    let current = collect_heads(
        &read.open_table(tables::PER_CELL_RECEIPT_HEAD_CURRENT_V1)?,
        "current per-cell receipt-head",
    )?;
    let live_records = collect_live_records(
        &read.open_table(tables::COMMIT_LOG)?,
        compacted_floor,
        cursor,
    )?;
    let expected = reconstruct_projection(compacted_floor, cursor, &baseline, &live_records)?;
    require_exact_projection(&expected, &current)?;
    Ok((compacted_floor, cursor, baseline, current, live_records))
}

/// The validated `current` projection as of one commit cursor, kept so the
/// next read replays only the records appended since.
struct CachedProjection {
    generation: u64,
    compacted_floor: u64,
    cursor: u64,
    current: BTreeMap<[u8; 32], HeadValue>,
}

/// Rewrite bookkeeping: `generation` advances when a non-append writer starts
/// and again when it ends; `in_flight` counts writers between those points.
#[derive(Default)]
struct RewriteEpoch {
    generation: u64,
    in_flight: u64,
}

/// Process-local cache behind [`PersistentStore::per_cell_receipt_heads_v1`].
///
/// A fresh finalized commit only appends: it writes the record at the cursor,
/// advances the cursor, and stages exactly that record's heads into `current`.
/// Every other writer of the commit log or either head table (compaction,
/// tail truncation, index rebuild, migration) holds a [`RewriteGuard`] for its
/// whole transaction, which invalidates the cache. A cached projection is
/// reused only when no such writer ran or is running, so replaying the
/// appended suffix yields what the full reconstruction would.
#[derive(Default)]
pub(crate) struct PerCellReceiptHeadCache {
    epoch: std::sync::Mutex<RewriteEpoch>,
    projection: std::sync::Mutex<Option<CachedProjection>>,
}

pub(crate) struct RewriteGuard<'a>(&'a PerCellReceiptHeadCache);

impl PerCellReceiptHeadCache {
    fn lock_epoch(&self) -> std::sync::MutexGuard<'_, RewriteEpoch> {
        self.epoch
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }

    /// `Some(generation)` when no rewriting writer is in flight.
    fn quiet_generation(&self) -> Option<u64> {
        let epoch = self.lock_epoch();
        (epoch.in_flight == 0).then_some(epoch.generation)
    }

    /// Mark a non-append write. Take it BEFORE `begin_write` and hold it past
    /// `commit`.
    pub(crate) fn begin_rewrite(&self) -> RewriteGuard<'_> {
        let mut epoch = self.lock_epoch();
        epoch.generation += 1;
        epoch.in_flight += 1;
        RewriteGuard(self)
    }
}

impl Drop for RewriteGuard<'_> {
    fn drop(&mut self) {
        let mut epoch = self.0.lock_epoch();
        epoch.generation += 1;
        epoch.in_flight -= 1;
    }
}

/// Advance `cached` to `cursor` by replaying only the appended records, with
/// the same per-record checks as [`reconstruct_projection`], then require the
/// durable `current` table to equal the cached projection exactly — one
/// O(cells) pass over the table, not a replay of history. `Ok(false)` means
/// "not provably an append": the caller rebuilds in full.
fn advance_cached_projection(
    read: &ReadTransaction,
    cached: &mut CachedProjection,
    compacted_floor: u64,
    cursor: u64,
) -> Result<bool> {
    if compacted_floor != cached.compacted_floor || cursor < cached.cursor {
        return Ok(false);
    }
    let live = cursor
        .checked_sub(compacted_floor)
        .ok_or_else(|| integrity("per-cell receipt-head cursor is behind compaction floor"))?;
    bounded_len(
        live,
        MAX_PER_CELL_RECEIPT_LIVE_RECORDS_V1,
        "live per-cell receipt-head commit suffix",
    )?;
    let log = read.open_table(tables::COMMIT_LOG)?;
    if log.len()? != live {
        return Ok(false);
    }
    let mut expected = cached.cursor;
    for entry in log.range(cached.cursor..cursor)? {
        let (key, bytes) =
            entry.map_err(|error: redb::StorageError| StoreError::Database(error.to_string()))?;
        let record = decode_commit_record(bytes.value())?;
        if key.value() != expected || record.ordinal != expected {
            return Ok(false);
        }
        let head = HeadValue {
            writer_ordinal: record.ordinal,
            receipt_hash: record.receipt_hash,
        };
        for cell in record_participants(&record)? {
            cached.current.insert(cell, head);
        }
        bounded_len(
            u64::try_from(cached.current.len()).unwrap_or(u64::MAX),
            MAX_PER_CELL_RECEIPT_HEADS_V1,
            "current per-cell receipt-head",
        )?;
        expected += 1;
    }
    if expected != cursor {
        return Ok(false);
    }
    let durable = read.open_table(tables::PER_CELL_RECEIPT_HEAD_CURRENT_V1)?;
    if usize::try_from(durable.len()?).ok() != Some(cached.current.len()) {
        return Ok(false);
    }
    for entry in durable.iter()? {
        let (cell, encoded) =
            entry.map_err(|error: redb::StorageError| StoreError::Database(error.to_string()))?;
        if cached.current.get(cell.value()) != Some(&decode_head(encoded.value())) {
            return Ok(false);
        }
    }
    cached.cursor = cursor;
    Ok(true)
}

impl PersistentStore {
    /// The validated `current` per-cell receipt heads, sorted by cell.
    ///
    /// Equal to `load_per_cell_receipt_head_recovery_v1()?.current` when it
    /// succeeds, but a call after only fresh commits replays just the records
    /// appended since the previous call instead of decoding the whole live
    /// commit log, so it detects fewer corruptions than the full load. The
    /// incremental check still compares the durable `current` table against
    /// the cached projection in full — a forged, extra or missing row for any
    /// cell falls back to the full validation and refuses — while corruption
    /// of an OLD live commit-log record is detected only by the full path,
    /// which re-decodes every record. The first call, and any call after a
    /// compaction, truncation, index rebuild or failed incremental check,
    /// runs the full validation.
    pub fn per_cell_receipt_heads_v1(&self) -> Result<Vec<DurablePerCellReceiptHead>> {
        let cache = &self.per_cell_head_cache;
        let mut slot = cache.projection.lock().unwrap_or_else(|poisoned| {
            let mut slot = poisoned.into_inner();
            *slot = None;
            slot
        });
        let read = self.db.begin_read()?;
        // Read after the snapshot opens: a rewrite committed before it is
        // either finished (generation moved) or still in flight.
        let generation = cache.quiet_generation();
        let (version, compacted_floor, cursor) = index_meta(&read)?;
        let reused = match (slot.as_mut(), generation) {
            (Some(cached), Some(generation))
                if cached.generation == generation
                    && version == Some(PER_CELL_RECEIPT_HEAD_INDEX_VERSION_V1) =>
            {
                matches!(
                    advance_cached_projection(&read, cached, compacted_floor, cursor),
                    Ok(true)
                )
            }
            _ => false,
        };
        if !reused {
            *slot = None;
            let (compacted_floor, cursor, _, current, _) = projection_from_read(&read)?;
            let heads = rows(&current);
            // Cache only if no rewrite began after the snapshot opened.
            if let Some(generation) = generation
                && cache.quiet_generation() == Some(generation)
            {
                *slot = Some(CachedProjection {
                    generation,
                    compacted_floor,
                    cursor,
                    current,
                });
            }
            return Ok(heads);
        }
        let heads = slot
            .as_ref()
            .map(|cached| rows(&cached.current))
            .unwrap_or_default();
        // A rewrite that began after the snapshot opened makes the cache stale
        // for the next call, though this snapshot's answer stands.
        if cache.quiet_generation() != generation {
            *slot = None;
        }
        Ok(heads)
    }

    /// Install the v1 index on an uncompacted legacy image, or validate an
    /// already-installed image.  A legacy store with `floor > 0` fails closed:
    /// its compacted records' write sets no longer exist, so inventing an empty
    /// baseline would irreversibly erase provenance.
    pub(crate) fn migrate_per_cell_receipt_head_index_v1(&self) -> Result<()> {
        let _rewrite = self.per_cell_head_cache.begin_rewrite();
        let write = self.db.begin_write()?;
        let (version, compacted_floor, cursor) = {
            let meta = write.open_table(tables::METADATA)?;
            (
                meta.get(tables::META_PER_CELL_RECEIPT_HEAD_INDEX_VERSION_V1)?
                    .map(|value| value.value()),
                meta.get(tables::META_COMMIT_COMPACTED)?
                    .map(|value| value.value())
                    .unwrap_or(0),
                meta.get(tables::META_COMMIT_CURSOR)?
                    .map(|value| value.value())
                    .unwrap_or(0),
            )
        };

        match version {
            Some(PER_CELL_RECEIPT_HEAD_INDEX_VERSION_V1) => {
                let baseline = collect_heads(
                    &write.open_table(tables::PER_CELL_RECEIPT_HEAD_BASELINE_V1)?,
                    "baseline per-cell receipt-head",
                )?;
                let current = collect_heads(
                    &write.open_table(tables::PER_CELL_RECEIPT_HEAD_CURRENT_V1)?,
                    "current per-cell receipt-head",
                )?;
                let records = collect_live_records(
                    &write.open_table(tables::COMMIT_LOG)?,
                    compacted_floor,
                    cursor,
                )?;
                let expected =
                    reconstruct_projection(compacted_floor, cursor, &baseline, &records)?;
                require_exact_projection(&expected, &current)?;
            }
            None => {
                let baseline = collect_heads(
                    &write.open_table(tables::PER_CELL_RECEIPT_HEAD_BASELINE_V1)?,
                    "baseline per-cell receipt-head",
                )?;
                let current = collect_heads(
                    &write.open_table(tables::PER_CELL_RECEIPT_HEAD_CURRENT_V1)?,
                    "current per-cell receipt-head",
                )?;
                if !baseline.is_empty() || !current.is_empty() {
                    return Err(integrity(
                        "unversioned per-cell receipt-head tables are nonempty",
                    ));
                }
                if compacted_floor != 0 {
                    return Err(integrity(format!(
                        "cannot migrate per-cell receipt heads after commit-log compaction floor {compacted_floor}: compacted write sets are unavailable"
                    )));
                }
                let records = collect_live_records(
                    &write.open_table(tables::COMMIT_LOG)?,
                    compacted_floor,
                    cursor,
                )?;
                let expected = reconstruct_projection(0, cursor, &baseline, &records)?;
                install_current(&write, &expected)?;
                let mut meta = write.open_table(tables::METADATA)?;
                meta.insert(
                    tables::META_PER_CELL_RECEIPT_HEAD_INDEX_VERSION_V1,
                    PER_CELL_RECEIPT_HEAD_INDEX_VERSION_V1,
                )?;
            }
            Some(other) => {
                return Err(integrity(format!(
                    "unknown per-cell receipt-head index version {other}"
                )));
            }
        }
        write.commit()?;
        Ok(())
    }

    /// Load and independently validate the complete restart image.
    pub fn load_per_cell_receipt_head_recovery_v1(&self) -> Result<PerCellReceiptHeadRecovery> {
        let read = self.db.begin_read()?;
        let (compacted_floor, cursor, baseline, current, live_records) =
            projection_from_read(&read)?;
        Ok(PerCellReceiptHeadRecovery {
            compacted_floor,
            cursor,
            baseline: rows(&baseline),
            current: rows(&current),
            live_records,
        })
    }
}

/// Advance every touched/removed cell to a freshly committed generic receipt.
/// Called inside the finalized-turn redb writer before the cursor is published.
pub(crate) fn stage_fresh_per_cell_receipt_heads_in(
    write: &WriteTransaction,
    record: &CommitRecord,
) -> Result<()> {
    let participants = record_participants(record)?;
    let mut current = write.open_table(tables::PER_CELL_RECEIPT_HEAD_CURRENT_V1)?;
    let mut count = current.len()?;
    bounded_len(
        count,
        MAX_PER_CELL_RECEIPT_HEADS_V1,
        "current per-cell receipt-head",
    )?;
    let successor = HeadValue {
        writer_ordinal: record.ordinal,
        receipt_hash: record.receipt_hash,
    };
    for cell in participants {
        match current.get(&cell)? {
            Some(encoded) => {
                let predecessor = decode_head(encoded.value());
                if predecessor.writer_ordinal >= record.ordinal {
                    return Err(integrity(format!(
                        "fresh commit {} would overwrite per-cell receipt head {:?} at non-predecessor ordinal {}",
                        record.ordinal,
                        CellId(cell),
                        predecessor.writer_ordinal
                    )));
                }
            }
            None => {
                count = count
                    .checked_add(1)
                    .ok_or_else(|| integrity("current per-cell receipt-head count overflow"))?;
                bounded_len(
                    count,
                    MAX_PER_CELL_RECEIPT_HEADS_V1,
                    "current per-cell receipt-head",
                )?;
            }
        }
        let encoded = encode_head(successor);
        current.insert(&cell, &encoded)?;
    }
    Ok(())
}

/// Verify an idempotent replay without repairing or mutating the index.
///
/// A cell may legitimately name a later writer because callers can replay an
/// older still-live ordinal.  Missing/older rows, or a same-ordinal different
/// hash, are integrity failures.
pub(crate) fn verify_replayed_per_cell_receipt_heads_in(
    write: &WriteTransaction,
    record: &CommitRecord,
) -> Result<()> {
    let current = write.open_table(tables::PER_CELL_RECEIPT_HEAD_CURRENT_V1)?;
    bounded_len(
        current.len()?,
        MAX_PER_CELL_RECEIPT_HEADS_V1,
        "current per-cell receipt-head",
    )?;
    for cell in record_participants(record)? {
        let encoded = current.get(&cell)?.ok_or_else(|| {
            integrity(format!(
                "replayed commit {} has no durable per-cell receipt head for {:?}",
                record.ordinal,
                CellId(cell)
            ))
        })?;
        let head = decode_head(encoded.value());
        if head.writer_ordinal < record.ordinal
            || (head.writer_ordinal == record.ordinal && head.receipt_hash != record.receipt_hash)
        {
            return Err(integrity(format!(
                "replayed commit {} disagrees with durable per-cell receipt head for {:?}",
                record.ordinal,
                CellId(cell)
            )));
        }
    }
    Ok(())
}

/// Fold the contiguous doomed live prefix into the compacted baseline.
///
/// The caller advances `META_COMMIT_COMPACTED` in the same transaction only
/// after this succeeds.  `current` is deliberately unchanged: compaction does
/// not change the latest writer, only which layer can reconstruct it.
pub(crate) fn fold_compacted_per_cell_receipt_heads_in(
    write: &WriteTransaction,
    old_floor: u64,
    records: &[CommitRecord],
) -> Result<()> {
    let record_count = u64::try_from(records.len())
        .map_err(|_| integrity("compacted per-cell receipt-head record count does not fit u64"))?;
    bounded_len(
        record_count,
        MAX_PER_CELL_RECEIPT_LIVE_RECORDS_V1,
        "compacted per-cell receipt-head record prefix",
    )?;
    let new_floor = old_floor
        .checked_add(record_count)
        .ok_or_else(|| integrity("per-cell receipt-head compaction floor overflow"))?;

    let mut baseline = collect_heads(
        &write.open_table(tables::PER_CELL_RECEIPT_HEAD_BASELINE_V1)?,
        "baseline per-cell receipt-head",
    )?;
    validate_baseline(old_floor, &baseline)?;
    for (index, record) in records.iter().enumerate() {
        let index = u64::try_from(index)
            .map_err(|_| integrity("compacted per-cell receipt-head index does not fit u64"))?;
        let expected = old_floor
            .checked_add(index)
            .ok_or_else(|| integrity("compacted per-cell receipt-head ordinal overflow"))?;
        if record.ordinal != expected {
            return Err(integrity(format!(
                "compacted per-cell receipt-head record ordinal {} is not dense expected ordinal {expected}",
                record.ordinal
            )));
        }
        let head = HeadValue {
            writer_ordinal: record.ordinal,
            receipt_hash: record.receipt_hash,
        };
        for cell in record_participants(record)? {
            baseline.insert(cell, head);
        }
        bounded_len(
            u64::try_from(baseline.len()).unwrap_or(u64::MAX),
            MAX_PER_CELL_RECEIPT_HEADS_V1,
            "baseline per-cell receipt-head",
        )?;
    }
    validate_baseline(new_floor, &baseline)?;

    let mut table = write.open_table(tables::PER_CELL_RECEIPT_HEAD_BASELINE_V1)?;
    for (cell, head) in baseline {
        let encoded = encode_head(head);
        table.insert(&cell, &encoded)?;
    }
    Ok(())
}

/// Replace `current` with `baseline` plus the surviving dense suffix.
///
/// This is the rollback primitive for divergent-tail recovery and the
/// compaction-aware extension of `rebuild_index_from_log`.
pub(crate) fn rebuild_current_per_cell_receipt_heads_in(
    write: &WriteTransaction,
    compacted_floor: u64,
    cursor: u64,
    live_records: &[CommitRecord],
) -> Result<()> {
    let baseline = collect_heads(
        &write.open_table(tables::PER_CELL_RECEIPT_HEAD_BASELINE_V1)?,
        "baseline per-cell receipt-head",
    )?;
    let expected = reconstruct_projection(compacted_floor, cursor, &baseline, live_records)?;
    install_current(write, &expected)
}

/// Strict audit hook for callers which already own a redb read transaction.
pub(crate) fn verify_per_cell_receipt_head_index_in(read: &ReadTransaction) -> Result<()> {
    projection_from_read(read).map(|_| ())
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::Cell;

    fn cell(marker: u8) -> Cell {
        Cell::with_balance(
            [marker; 32],
            [marker.wrapping_add(1); 32],
            i64::from(marker),
        )
    }

    fn record(
        ordinal: u64,
        marker: u8,
        touched_cells: Vec<Cell>,
        removed: Vec<CellId>,
    ) -> CommitRecord {
        CommitRecord {
            ordinal,
            height: ordinal + 1,
            block_id: [marker.wrapping_add(1); 32],
            block_executed_up_to: ordinal + 1,
            turn_hash: [marker.wrapping_add(2); 32],
            creator: [marker.wrapping_add(3); 32],
            receipt_hash: [marker; 32],
            ledger_root: [marker.wrapping_add(4); 32],
            touched_cells,
            removed: removed.into_iter().map(|cell| cell.0).collect(),
        }
    }

    #[test]
    fn fixed_head_codec_round_trips_ordinal_and_full_hash() {
        let head = HeadValue {
            writer_ordinal: 0x0102_0304_0506_0708,
            receipt_hash: [0xA5; 32],
        };
        let encoded = encode_head(head);
        assert_eq!(&encoded[..8], &head.writer_ordinal.to_le_bytes());
        assert_eq!(&encoded[8..], &head.receipt_hash);
        assert_eq!(decode_head(&encoded), head);
    }

    #[test]
    fn compacted_baseline_plus_live_removal_is_last_writer_wins() {
        let a = cell(0xA1);
        let b = cell(0xB1);
        let a_id = a.id();
        let b_id = b.id();
        let baseline = BTreeMap::from([(
            a_id.0,
            HeadValue {
                writer_ordinal: 0,
                receipt_hash: [0x10; 32],
            },
        )]);
        let records = vec![record(1, 0x20, vec![b], vec![a_id])];
        let projection = reconstruct_projection(1, 2, &baseline, &records).unwrap();
        assert_eq!(projection[&a_id.0].writer_ordinal, 1);
        assert_eq!(projection[&a_id.0].receipt_hash, [0x20; 32]);
        assert_eq!(projection[&b_id.0].writer_ordinal, 1);
    }

    #[test]
    fn duplicate_touched_removed_participant_refuses() {
        let a = cell(0xA2);
        let a_id = a.id();
        let hostile = record(0, 0x30, vec![a], vec![a_id]);
        let error = reconstruct_projection(0, 1, &BTreeMap::new(), &[hostile]).unwrap_err();
        assert!(
            error
                .to_string()
                .contains("more than once across touched/removed")
        );
    }

    fn full_current(store: &PersistentStore) -> Result<Vec<DurablePerCellReceiptHead>> {
        store
            .load_per_cell_receipt_head_recovery_v1()
            .map(|recovery| recovery.current)
    }

    fn overwrite_current_row(store: &PersistentStore, cell: CellId, head: HeadValue) {
        let write = store.db.begin_write().unwrap();
        write
            .open_table(tables::PER_CELL_RECEIPT_HEAD_CURRENT_V1)
            .unwrap()
            .insert(&cell.0, &encode_head(head))
            .unwrap();
        write.commit().unwrap();
    }

    /// After every one of N interleaved commits (with a removal) and across a
    /// compaction and an index rebuild, the incremental heads equal the full
    /// rebuild's.
    #[test]
    fn incremental_heads_equal_the_full_rebuild_after_each_commit() {
        let store = PersistentStore::open_in_memory().unwrap();
        assert_eq!(store.per_cell_receipt_heads_v1().unwrap(), Vec::new());
        let cells: Vec<Cell> = (0..4).map(|i| cell(0x50 + i)).collect();
        for ordinal in 0..12u64 {
            let touched = vec![
                cells[ordinal as usize % 4].clone(),
                cells[(ordinal as usize + 1) % 4].clone(),
            ];
            let removed = if ordinal == 7 {
                vec![cells[2].id()]
            } else {
                vec![]
            };
            let touched = touched
                .into_iter()
                .filter(|c| !removed.contains(&c.id()))
                .collect();
            let marker = 0x60 + ordinal as u8;
            store
                .commit_finalized_turn(ordinal, &record(ordinal, marker, touched, removed))
                .unwrap();
            assert_eq!(
                store.per_cell_receipt_heads_v1().unwrap(),
                full_current(&store).unwrap(),
                "after commit {ordinal}"
            );
        }

        store
            .store_ledger_checkpoint_snapshot(&crate::LedgerCheckpoint {
                height: 6,
                cells: Vec::new(),
                sovereign_commitments: Vec::new(),
                sovereign_registrations: Vec::new(),
            })
            .unwrap();
        assert!(store.compact_below_with_test_poa_anchor_v1(6).unwrap() > 0);
        assert_eq!(
            store.per_cell_receipt_heads_v1().unwrap(),
            full_current(&store).unwrap()
        );
        store
            .commit_finalized_turn(12, &record(12, 0x7C, vec![cells[3].clone()], vec![]))
            .unwrap();
        store.rebuild_index_from_log().unwrap();
        assert_eq!(
            store.per_cell_receipt_heads_v1().unwrap(),
            full_current(&store).unwrap()
        );
    }

    /// A durable `current` row that disagrees with the replayed record refuses
    /// exactly as the full rebuild does, and so does an extra row.
    #[test]
    fn incremental_heads_refuse_a_current_row_mismatch() {
        let store = PersistentStore::open_in_memory().unwrap();
        let a = cell(0x81);
        let b = cell(0x82);
        store
            .commit_finalized_turn(0, &record(0, 0x90, vec![a.clone()], vec![]))
            .unwrap();
        store.per_cell_receipt_heads_v1().unwrap();
        store
            .commit_finalized_turn(1, &record(1, 0x91, vec![a.clone()], vec![]))
            .unwrap();
        let forged = HeadValue {
            writer_ordinal: 1,
            receipt_hash: [0xEE; 32],
        };
        overwrite_current_row(&store, a.id(), forged);
        let full = full_current(&store).unwrap_err().to_string();
        let incremental = store.per_cell_receipt_heads_v1().unwrap_err().to_string();
        assert_eq!(incremental, full);
        assert!(incremental.contains("disagrees with compacted baseline plus live suffix"));

        let store = PersistentStore::open_in_memory().unwrap();
        store
            .commit_finalized_turn(0, &record(0, 0x92, vec![a.clone()], vec![]))
            .unwrap();
        store.per_cell_receipt_heads_v1().unwrap();
        store
            .commit_finalized_turn(1, &record(1, 0x93, vec![a], vec![]))
            .unwrap();
        overwrite_current_row(&store, b.id(), forged);
        assert!(full_current(&store).is_err());
        assert!(store.per_cell_receipt_heads_v1().is_err());
    }

    /// A forged durable `current` row for a cell NOT advanced since the cache
    /// was warmed falls back to the full rebuild and refuses exactly as it
    /// does; the incremental check must not accept it just because the forged
    /// cell was not touched by the appended records.
    #[test]
    fn incremental_heads_fall_back_on_a_forged_row_for_a_non_advanced_cell() {
        let store = PersistentStore::open_in_memory().unwrap();
        let a = cell(0x83);
        let b = cell(0x84);
        store
            .commit_finalized_turn(
                0,
                &record(0, 0x94, vec![a.clone(), b.clone()], vec![]),
            )
            .unwrap();
        store.per_cell_receipt_heads_v1().unwrap();
        // Commit 1 advances only `a`, so `b` is not advanced since the warm.
        store
            .commit_finalized_turn(1, &record(1, 0x95, vec![a.clone()], vec![]))
            .unwrap();
        let forged = HeadValue {
            writer_ordinal: 0,
            receipt_hash: [0xEF; 32],
        };
        overwrite_current_row(&store, b.id(), forged);
        assert!(full_current(&store).is_err());
        let full = full_current(&store).unwrap_err().to_string();
        let incremental = store.per_cell_receipt_heads_v1().unwrap_err().to_string();
        assert_eq!(incremental, full);
        assert!(incremental.contains("disagrees with compacted baseline plus live suffix"));
    }

    /// The warm path decodes only appended records: an undecodable OLD live
    /// record breaks the full load but not the incremental one. Without the
    /// cache every call decodes the whole live log and this refuses.
    #[test]
    fn incremental_heads_do_not_redecode_the_live_log() {
        let store = PersistentStore::open_in_memory().unwrap();
        let a = cell(0xA4);
        let b = cell(0xB4);
        store
            .commit_finalized_turn(0, &record(0, 0xC0, vec![a.clone()], vec![]))
            .unwrap();
        store.per_cell_receipt_heads_v1().unwrap();
        let write = store.db.begin_write().unwrap();
        write
            .open_table(tables::COMMIT_LOG)
            .unwrap()
            .insert(0u64, [0xFFu8; 2].as_slice())
            .unwrap();
        write.commit().unwrap();
        store
            .commit_finalized_turn(1, &record(1, 0xC1, vec![b.clone()], vec![]))
            .unwrap();
        assert!(full_current(&store).is_err());
        let heads = store.per_cell_receipt_heads_v1().unwrap();
        assert_eq!(heads.len(), 2);
        assert!(
            heads
                .iter()
                .any(|h| h.cell == b.id() && h.writer_ordinal == 1)
        );
    }

    #[test]
    fn legacy_compacted_store_without_baseline_fails_closed() {
        let store = PersistentStore::open_in_memory().unwrap();
        let a = cell(0xA3);
        store
            .commit_finalized_turn(0, &record(0, 0x40, vec![a], vec![]))
            .unwrap();
        store
            .store_ledger_checkpoint_snapshot(&crate::LedgerCheckpoint {
                height: 2,
                cells: Vec::new(),
                sovereign_commitments: Vec::new(),
                sovereign_registrations: Vec::new(),
            })
            .unwrap();
        assert_eq!(store.compact_below_with_test_poa_anchor_v1(2).unwrap(), 1);

        // Model a pre-v1 image: compaction history exists, but neither the
        // schema marker nor either durable projection was carried forward.
        let write = store.db.begin_write().unwrap();
        {
            let mut meta = write.open_table(tables::METADATA).unwrap();
            meta.remove(tables::META_PER_CELL_RECEIPT_HEAD_INDEX_VERSION_V1)
                .unwrap();
        }
        clear_head_table(&write, tables::PER_CELL_RECEIPT_HEAD_BASELINE_V1).unwrap();
        clear_head_table(&write, tables::PER_CELL_RECEIPT_HEAD_CURRENT_V1).unwrap();
        write.commit().unwrap();

        let error = store.migrate_per_cell_receipt_head_index_v1().unwrap_err();
        assert!(
            error
                .to_string()
                .contains("compacted write sets are unavailable")
        );
    }
}
