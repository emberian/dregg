//! Durable, crash-consistent commit log + secondary index.
//!
//! # What problem this solves
//!
//! Before this module, the node's recovery anchor (`executed_up_to`) and the
//! finalized ledger state were persisted by *independent* transactions at
//! *different* cadences: `executed_up_to` advanced every batch
//! (`blocklace_sync::persist_blocklace_state`), while the ledger was
//! checkpointed only every `LEDGER_CHECKPOINT_INTERVAL` blocks
//! (`blocklace_sync::maybe_checkpoint_ledger`). A crash between those two writes
//! left the durable `executed_up_to` ahead of the durable ledger, and recovery
//! performed **no replay** for the gap — so every finalized turn between the
//! last ledger checkpoint and `executed_up_to` was silently lost from the
//! restored ledger (torn state). Receipts were never persisted at all
//! (the cipherclerk chain lived only in RAM).
//!
//! # The commit log
//!
//! The commit log is the authoritative, append-only record of the turns THIS
//! node has applied, in the node's tau-finalized order. Each [`CommitRecord`]
//! is written in the **same redb transaction** that:
//!   * advances the durable commit cursor ([`tables::META_COMMIT_CURSOR`]),
//!   * inserts the per-turn index entries (receipt-by-hash, turn-by-hash,
//!     turn-by-(height, creator)), and
//!   * upserts the per-turn cell snapshots into the cell-by-id index.
//!
//! redb is an ACID store: a transaction either fully commits (durably, with an
//! fsync at the commit boundary) or does not appear at all. Because all of the
//! above land in one transaction, the following invariants hold across an
//! arbitrary crash (even one that kills the process mid-write):
//!
//!   * **No torn state.** The cursor and the record at `cursor-1` are always
//!     consistent: every ordinal in `[compacted_floor, cursor)` resolves to a
//!     record, and `commit_cursor() == commit_log.len() + compacted_floor`
//!     (the `compacted_floor == 0` special case is the pre-compaction
//!     `cursor == len`; see [`Self::compact_below`]).
//!   * **No lost finalized turn.** A turn the node *durably* committed is
//!     recoverable with its full coordinates and the post-state of every cell it
//!     touched — either from its log record, OR (once [`Self::compact_below`]
//!     has removed that record under a covering checkpoint) from the checkpoint
//!     that subsumes it. Compaction never removes a record a checkpoint does not
//!     subsume, so the finalized state is never lost.
//!   * **No double-apply.** Recovery resumes from `commit_cursor()`, which is
//!     advanced once per applied turn inside the commit transaction; a turn whose
//!     transaction did not commit is simply re-applied (idempotently) on the
//!     next poll, and one whose transaction *did* commit is never re-applied.
//!     This holds across compaction: a compacted turn's `block_id` is retained
//!     (`COMMIT_COMPACTED_BLOCK_IDS`) and still reported by
//!     [`Self::commit_log_block_ids`], so the identity execution cursor still
//!     sees it as applied and never re-executes it on top of the checkpoint.
//!   * **Index agrees with the log.** Every index entry exists *iff* the commit
//!     log has the corresponding record. [`PersistentStore::verify_index_agrees_with_log`]
//!     checks this; [`PersistentStore::rebuild_index_from_log`] re-derives the
//!     entire index from the log alone.
//!
//! The commit cursor is the crash-consistent replacement for the prior
//! separately-written `executed_up_to`; recovery reads it via
//! [`PersistentStore::commit_cursor`].
//!
//! # Layering
//!
//! This module stays independent of `dregg-turn`: the node hashes the turn /
//! receipt coordinates and passes them in as plain bytes, alongside the
//! `(CellId, Cell)` snapshots of every cell the turn touched. `dregg-cell` is
//! already a dependency, so cell snapshots are serialized here.

use redb::{ReadableTable, ReadableTableMetadata};
use serde::{Deserialize, Serialize};

use dregg_cell::{Cell, CellId};
use dregg_federation::frost::MlDsaPublicKey;
use dregg_types::PublicKey;

use crate::tables;
use crate::{
    FaithfulNoteRootAnchorV1, FaithfulNoteRootEnvelopeV1, Poseidon2NoteTree, StoredAttestedRoot,
};
use crate::{PersistentStore, Result, StoreError};

/// Production note-tree depth.  The live node and durable reconstruction must
/// use the same positional shape or a correct leaf sequence would attest a
/// different root after restart.
const LIVE_NOTE_TREE_DEPTH: usize = 16;

/// The faithful-root half of one finalized atomic commit.
///
/// `author_*` is the exact enrolled node identity that hybrid-authenticated the
/// history record.  It is intentionally a one-author authentication boundary,
/// not mislabeled as the later federation finality quorum: the carrying block
/// supplies finality, while this signature prevents an offline store attacker
/// without the node's keys from forging a history row across restart.
pub struct FinalizedFaithfulRootWeld<'a> {
    /// Required only for the first record of a migrated/fresh v1 segment.
    pub initial_anchor: Option<&'a FaithfulNoteRootAnchorV1>,
    pub envelope: &'a FaithfulNoteRootEnvelopeV1,
    pub author_committee: &'a [PublicKey],
    pub author_ml_dsa_committee: &'a [MlDsaPublicKey],
    pub attested_root: &'a StoredAttestedRoot,
    /// Every `NoteSpend` finalized by this turn, in deterministic DFS effect
    /// order.  These records are inserted into the durable nullifier
    /// accumulator in the same transaction as the carrying commit and root.
    pub spent_nullifiers: &'a [FinalizedNullifierRecord],
    /// Full public FNSP-v2 statements in the same deterministic order as
    /// `spent_nullifiers`.  Persistence validates every staged successor root
    /// before minting the neutral finalized-spend authorities consumed by
    /// games/markets.
    pub finalized_spends: &'a [crate::FinalizedFaithfulSpendInput],
}

/// Unforgeable proof that one Galley candidate is being derived from the
/// finalized-turn writer's already-validated receipt/faithful/executor weld.
///
/// This is deliberately a capability, not another caller-authored finality
/// carrier.  Only this module can construct it, and the production constructor
/// belongs at the point inside [`PersistentStore::commit_finalized_turn_welded`]
/// where the exact receipt and its carrying record have passed the central
/// writer's checks.  The Galley authority module may read the coordinates only
/// to re-bind its independently authenticated `SignedTurn`; it cannot mint,
/// clone, serialize, or retain this proof across transactions.
pub(crate) struct ValidatedPoaGalleyFinalityWeldV1 {
    ordinal: u64,
    block_id: [u8; 32],
    turn_hash: [u8; 32],
    receipt_hash: [u8; 32],
}

impl ValidatedPoaGalleyFinalityWeldV1 {
    pub(crate) fn ordinal(&self) -> u64 {
        self.ordinal
    }

    pub(crate) fn block_id(&self) -> [u8; 32] {
        self.block_id
    }

    pub(crate) fn turn_hash(&self) -> [u8; 32] {
        self.turn_hash
    }

    pub(crate) fn receipt_hash(&self) -> [u8; 32] {
        self.receipt_hash
    }
}

/// The public accumulator input carried by one finalized `NoteSpend`.
///
/// `value` is already public in the deployed note-spend statement.  Persisting
/// it is necessary because the circuit-faithful nullifier leaf commits to both
/// the revealed nullifier and this value; a bare presence bit cannot reproduce
/// the accepted root after restart.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FinalizedNullifierRecord {
    pub nullifier: [u8; 32],
    pub value: u64,
}

/// How the immutable receipt row participates in a finalized-turn transaction.
///
/// Ordinary federation finalization owns the receipt append, while solo
/// finalization may be completing custody for a receipt that ingress already
/// durably appended.  Keeping those cases distinct prevents the latter from
/// silently repairing a missing receipt row at the tail and calling the image
/// consistent.
enum ReceiptWeldMode<'a> {
    /// Append at the dense tail, or verify a byte-identical row on retry.
    AppendOrVerify { index: u64, encoded: &'a [u8] },
    /// Require a byte-identical row that predates this transaction.
    ExistingExact { index: u64, encoded: &'a [u8] },
}

/// Raw, caller-untrusted Galley material retained only until the central writer
/// has validated the exact receipt, faithful edge, and executor projection.
/// It is never itself authority and never crosses a persistence boundary.
struct PoaGalleyRawWeld<'a> {
    signed_turn: &'a dregg_turn::SignedTurn,
    receipt: &'a dregg_turn::TurnReceipt,
}

enum ExactFnspV3Weld {
    #[cfg(test)]
    AccumulatorOnly(crate::ExactFnspV3StateCasV1),
    Frame {
        exact: crate::ExactFnspV3StateCasV1,
        activation: Option<crate::UntrustedExactFnspV3ActivationV1>,
        frame: crate::UntrustedExactFnspV3FrameV1,
    },
}

impl ExactFnspV3Weld {
    const fn exact(&self) -> crate::ExactFnspV3StateCasV1 {
        match self {
            #[cfg(test)]
            Self::AccumulatorOnly(exact) => *exact,
            Self::Frame { exact, .. } => *exact,
        }
    }
}

impl ReceiptWeldMode<'_> {
    fn entry(&self) -> (u64, &[u8]) {
        match self {
            Self::AppendOrVerify { index, encoded } | Self::ExistingExact { index, encoded } => {
                (*index, encoded)
            }
        }
    }

    fn allow_insert(&self) -> bool {
        matches!(self, Self::AppendOrVerify { .. })
    }
}

/// One durable record of a finalized turn this node applied to its ledger.
///
/// Stored in [`tables::COMMIT_LOG`] keyed by the commit ordinal (its dense,
/// gap-free position in the node's applied order). Carries everything needed to
/// (a) anchor recovery, (b) drive the secondary index, and (c) re-derive the
/// index from the log alone.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CommitRecord {
    /// The commit ordinal: this record's position in the applied order. Equals
    /// the redb key it is stored under. Dense and gap-free: `ordinal == n` means
    /// exactly `n` turns were applied before it.
    pub ordinal: u64,
    /// The node-assigned height this turn committed at (the attested-root height
    /// for the turn). Used by the `(height, creator)` index.
    pub height: u64,
    /// The blocklace block id that carried this turn (consensus anchor).
    pub block_id: [u8; 32],
    /// The blocklace block-level high-water mark (`executed_up_to`) AS OF this
    /// turn's commit. Persisted here, inside the same atomic transaction, so that
    /// recovery reads a block cursor that can never be torn ahead of the durable
    /// ledger: the node resumes block processing from the last committed turn's
    /// `block_executed_up_to`. (Non-turn blocks — membership/checkpoint — are
    /// idempotent on re-process, so only turns need the no-double-apply guard the
    /// commit log itself provides.)
    pub block_executed_up_to: u64,
    /// The turn hash (`Turn::hash`).
    pub turn_hash: [u8; 32],
    /// The agent/creator cell id of the turn.
    pub creator: [u8; 32],
    /// The receipt hash (`TurnReceipt::receipt_hash`) produced by applying it.
    pub receipt_hash: [u8; 32],
    /// The canonical ledger root AFTER this turn was applied. Binds the record
    /// to a concrete post-state so recovery can assert convergence.
    pub ledger_root: [u8; 32],
    /// Post-state snapshots of every cell this turn touched (created/mutated).
    /// These feed the cell-by-id index. Serialized `dregg_cell::Cell`s.
    pub touched_cells: Vec<Cell>,
    /// Cell ids this turn REMOVED from the hosted set — the tombstone dimension
    /// (today: `MakeSovereign`, which lifts a cell out of the hosted ledger and
    /// keeps only its sovereign commitment). `touched_cells` is post-states only,
    /// so a removal is otherwise structurally invisible: the durable overlay
    /// (`cell_overlay_since`) and the cell-by-id index would RESURRECT the removed
    /// cell as hosted on `checkpoint ⊕ overlay` recovery, diverging the
    /// reconstructed root from `ledger_root`. The reconstruction applies these as
    /// deletions.
    ///
    /// BACK-COMPAT: this field was appended after the original layout. Postcard is
    /// non-self-describing, so a pre-`removed` durable record has no bytes for it;
    /// [`decode_commit_record`] falls back to the legacy layout and lifts such a
    /// record with an empty `removed`.
    #[serde(default)]
    pub removed: Vec<[u8; 32]>,
}

/// The pre-`removed` durable layout of [`CommitRecord`], for back-compatible
/// decode of records written before the tombstone dimension existed. Field order
/// mirrors `CommitRecord` exactly up to (but excluding) `removed`, so postcard
/// decodes a legacy blob into this and [`decode_commit_record`] lifts it.
#[derive(Deserialize)]
struct CommitRecordV0 {
    ordinal: u64,
    height: u64,
    block_id: [u8; 32],
    block_executed_up_to: u64,
    turn_hash: [u8; 32],
    creator: [u8; 32],
    receipt_hash: [u8; 32],
    ledger_root: [u8; 32],
    touched_cells: Vec<Cell>,
}

impl From<CommitRecordV0> for CommitRecord {
    fn from(v: CommitRecordV0) -> Self {
        CommitRecord {
            ordinal: v.ordinal,
            height: v.height,
            block_id: v.block_id,
            block_executed_up_to: v.block_executed_up_to,
            turn_hash: v.turn_hash,
            creator: v.creator,
            receipt_hash: v.receipt_hash,
            ledger_root: v.ledger_root,
            touched_cells: v.touched_cells,
            removed: Vec::new(),
        }
    }
}

/// Back-compatible decode of a durable [`CommitRecord`].
///
/// Tries the CURRENT layout first; new records always decode this way. A legacy
/// record (written before `removed`) lacks the trailing tombstone bytes and fails
/// the current decode with a short-buffer error — postcard is non-self-describing
/// — so we fall back to [`CommitRecordV0`] and lift it with an empty `removed`. A
/// legacy record can NEVER spuriously decode as current: the missing trailing
/// `Vec` length varint forces the shortfall, so the ordering is unambiguous.
pub(crate) fn decode_commit_record(bytes: &[u8]) -> Result<CommitRecord> {
    match postcard::from_bytes::<CommitRecord>(bytes) {
        Ok(rec) => Ok(rec),
        Err(_) => {
            let legacy: CommitRecordV0 = postcard::from_bytes(bytes)?;
            Ok(legacy.into())
        }
    }
}

/// One resolved cell-overlay operation for recovery: the durable last-writer-wins
/// effect on a single cell id since the checkpoint. Mirrors the Lean
/// `Dregg2.Distributed.CrashRecovery.Write` alphabet (`insert | remove`): the
/// recovery overlay is NOT insert-only, so a removal is carried, not dropped.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum CellOverlayOp {
    /// Install/overwrite the cell (a created/updated post-state). Applied as
    /// `Ledger::insert_cell` (last-writer-wins, remove-then-insert on recovery).
    Upsert(Cell),
    /// Delete the cell — a tombstone (it was removed from the hosted set, e.g.
    /// `MakeSovereign`). Applied as `Ledger::remove` on recovery, so the cell does
    /// not survive `checkpoint ⊕ overlay`.
    Remove(CellId),
}

/// Outcome of a welded finalized-turn commit.
///
/// Distinguishes a FRESH durable write (the record and its welded notes/burns
/// were just written in this transaction) from an IDEMPOTENT REPLAY (the turn
/// was already durably committed; this call wrote nothing). The caller needs
/// this to advance purely-in-RAM derived state (e.g. the node's in-RAM
/// Poseidon2 note tree) exactly once: only on a fresh write, never on a replay
/// (whose leaves the boot-time rebuild from the durable table already holds).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CommitOutcome {
    /// The commit ordinal the record occupies.
    pub ordinal: u64,
    /// True iff this call freshly wrote the record (and its welded notes/burns).
    /// False on an idempotent replay of an already-committed turn (no writes).
    pub freshly_committed: bool,
}

/// Durable success for the exact-frame apex.  The frame head has no public constructor and is
/// minted only after a fresh writer commit or after byte-exact replay verification.
pub struct ExactFnspV3FrameCommitOutcome {
    pub outcome: CommitOutcome,
    pub committed_head: crate::CommittedExactFnspV3FrameHeadV1,
    /// Signer-independent semantic identity minted and persisted in the same transaction.
    pub finalized_receipt_core_id: dregg_turn::FinalizedReceiptIdV1,
}

struct WeldedCommitOutcome {
    outcome: CommitOutcome,
    committed_head: Option<crate::CommittedExactFnspV3FrameHeadV1>,
    finalized_receipt_core_id: Option<dregg_turn::FinalizedReceiptIdV1>,
}

fn validate_faithful_commit_coordinates(
    record: &CommitRecord,
    faithful: &FinalizedFaithfulRootWeld<'_>,
) -> Result<()> {
    let edge = &faithful.envelope.record;
    let attested = faithful.attested_root;
    if edge.height != record.height
        || edge.block_id != record.block_id
        || attested.height != record.height
        || attested.blocklace_block_id != Some(record.block_id)
        || attested.federation_id.0 != edge.federation_id
        || attested.note_tree_root != Some(edge.successor.to_bytes())
    {
        return Err(StoreError::Integrity(
            "faithful note-root/commit/attestation coordinates disagree".to_string(),
        ));
    }
    Ok(())
}

/// Join the Lean-prepared PoA V2 coordinate to authority which persistence can
/// independently recover from the exact finalized receipt. This is the seam
/// which prevents an otherwise well-formed batch from naming an arbitrary
/// signer or actor root beside a genuine commit.
fn validate_poa_v2_batch_authority(
    record: &CommitRecord,
    encoded_receipt: &[u8],
    batch: &crate::PreparedPoaEventBatchV2,
    holding: Option<&crate::PreparedPoaHoldingConsumptionV1>,
) -> Result<()> {
    let receipt: dregg_turn::TurnReceipt = postcard::from_bytes(encoded_receipt).map_err(|_| {
        StoreError::Integrity("PoA V2 batch receipt is not canonical TurnReceipt bytes".to_string())
    })?;
    let canonical = postcard::to_stdvec(&receipt)
        .map_err(|error| StoreError::Serialization(error.to_string()))?;
    if canonical.as_slice() != encoded_receipt {
        return Err(StoreError::Integrity(
            "PoA V2 batch receipt encoding is not canonical".to_string(),
        ));
    }

    let coordinate = batch.coordinate();
    let signer_cell =
        dregg_cell::CellId::derive_raw(&coordinate.signer(), blake3::hash(b"default").as_bytes());
    if receipt.turn_hash != record.turn_hash
        || receipt.receipt_hash() != record.receipt_hash
        || receipt.pre_state_hash != coordinate.actor_root()
        || receipt.agent != signer_cell
        || receipt.federation_id != coordinate.world().federation_id()
    {
        return Err(StoreError::Integrity(
            "PoA V2 batch signer/actor/world coordinate disagrees with exact finalized receipt"
                .to_string(),
        ));
    }
    if let Some(holding) = holding
        && (holding.player() != coordinate.signer() || holding.player_cell() != receipt.agent.0)
    {
        return Err(StoreError::Integrity(
            "PoA holding player is not the exact finalized receipt signer/agent".to_string(),
        ));
    }
    Ok(())
}

/// Bind the one exact-v3 CAS candidate to the finalized spend carried by this turn.
///
/// The durable exact accumulator independently replays the state transition, but without this
/// join a caller could atomically append an unrelated `(nullifier, value)` beside an otherwise
/// valid receipt.  The current transport admits one exact append; multi-spend turns must use a
/// future ordered batch carrier rather than silently committing only a prefix.
fn validate_exact_fnsp_v3_finalization_coordinates(
    faithful: &FinalizedFaithfulRootWeld<'_>,
    exact: crate::ExactFnspV3StateCasV1,
) -> Result<()> {
    let [spend] = faithful.spent_nullifiers else {
        return Err(StoreError::Integrity(format!(
            "exact FNSP-v3 finalized-turn weld requires exactly one spent nullifier, got {}",
            faithful.spent_nullifiers.len()
        )));
    };
    let append = exact.append_record();
    if append.raw != spend.nullifier || append.value != spend.value {
        return Err(StoreError::Integrity(
            "exact FNSP-v3 append does not name the finalized turn's nullifier/value".to_string(),
        ));
    }
    Ok(())
}

fn decode_nullifier_record(bytes: &[u8; 16]) -> (u64, u64) {
    let mut value = [0u8; 8];
    value.copy_from_slice(&bytes[..8]);
    let mut seq = [0u8; 8];
    seq.copy_from_slice(&bytes[8..]);
    (u64::from_le_bytes(value), u64::from_le_bytes(seq))
}

fn encode_nullifier_record(value: u64, seq: u64) -> [u8; 16] {
    let mut out = [0u8; 16];
    out[..8].copy_from_slice(&value.to_le_bytes());
    out[8..].copy_from_slice(&seq.to_le_bytes());
    out
}

/// Reconstruct the exact circuit-facing nullifier accumulator from the two
/// durable tables inside the caller's write snapshot.  A legacy image with
/// presence rows but no value/sequence rows is intentionally refused: those
/// missing public inputs cannot be recovered honestly.
fn durable_faithful_nullifier_set_in(
    write: &redb::WriteTransaction,
) -> Result<dregg_cell::nullifier_set::NullifierSet> {
    let presence = write.open_table(tables::NULLIFIERS)?;
    let records = write.open_table(tables::NULLIFIER_RECORDS_V1)?;
    let presence_len = presence.len()?;
    let records_len = records.len()?;
    if presence_len != records_len {
        return Err(StoreError::Integrity(format!(
            "nullifier presence/record table lengths disagree ({presence_len} != {records_len}); \
             legacy nonempty images require an explicit value/sequence migration"
        )));
    }

    let record_capacity = usize::try_from(records_len).map_err(|_| {
        StoreError::Integrity("nullifier record count does not fit usize".to_string())
    })?;
    let mut decoded = Vec::with_capacity(record_capacity);
    let mut seen_seq = vec![false; record_capacity];
    for entry in records.iter()? {
        let entry = entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
        let nullifier = *entry.0.value();
        if presence.get(&nullifier)?.is_none() {
            return Err(StoreError::Integrity(
                "nullifier record has no matching spent-presence row".to_string(),
            ));
        }
        let (value, seq) = decode_nullifier_record(entry.1.value());
        let seq_index = usize::try_from(seq).map_err(|_| {
            StoreError::Integrity("nullifier append sequence does not fit usize".to_string())
        })?;
        if seq_index >= record_capacity || seen_seq[seq_index] {
            return Err(StoreError::Integrity(
                "nullifier append sequence is duplicated or outside the dense durable range"
                    .to_string(),
            ));
        }
        seen_seq[seq_index] = true;
        decoded.push((dregg_cell::note::Nullifier(nullifier), value, seq));
    }
    if seen_seq.iter().any(|seen| !seen) {
        return Err(StoreError::Integrity(
            "nullifier append sequence has a durable gap".to_string(),
        ));
    }
    dregg_cell::nullifier_set::NullifierSet::from_records(decoded).map_err(|e| {
        StoreError::Integrity(format!(
            "durable nullifier accumulator cannot be reconstructed: {e}"
        ))
    })
}

fn durable_faithful_exact_append_records_in(
    write: &redb::WriteTransaction,
) -> Result<Vec<dregg_circuit::exact_nullifier_aafi::ExactAppendRecord>> {
    Ok(durable_faithful_nullifier_set_in(write)?
        .iter_in_append_order()
        .map(
            |(nullifier, value, seq)| dregg_circuit::exact_nullifier_aafi::ExactAppendRecord {
                seq,
                raw: nullifier.0,
                value,
            },
        )
        .collect())
}

/// Require the exact-v3 and legacy faithful authorities to describe the same complete append
/// history during bootstrap/open/test-only activation, then pin that equality as the rolling live
/// induction boundary. This is deliberately O(N); live finalized turns use the O(1) bridge gate.
pub(crate) fn validate_exact_fnsp_v3_faithful_prefix_in(
    write: &redb::WriteTransaction,
) -> Result<()> {
    let legacy = durable_faithful_exact_append_records_in(write)?;
    let exact = crate::exact_fnsp_v3_state::exact_fnsp_v3_append_records_in(write)?;
    if exact != legacy {
        return Err(StoreError::Integrity(format!(
            "exact FNSP-v3 authority diverges from faithful nullifier records (exact {} records, faithful {})",
            exact.len(),
            legacy.len()
        )));
    }
    crate::exact_fnsp_v3_faithful_bridge::install_after_full_audit_in(write, &legacy)
}

/// Stage the faithful half of one exact FNSP-v3 append inside the caller's writer.
///
/// PRODUCTION never appends to one authority alone. [`PersistentStore::commit_finalized_turn_welded`]
/// writes the faithful presence/record rows (`append_fresh_nullifiers_in`), the exact append, and
/// the rolling bridge advance in ONE transaction, and refuses outright when only one of the two
/// bridge projections is staged. The two narrower exact-append seams —
/// [`PersistentStore::compare_and_commit_exact_fnsp_v3_append`] and
/// [`crate::exact_fnsp_v3_frame_head::stage_exact_fnsp_v3_frame_in`] — are test-only and carry no
/// faithful half of their own, so without this they durably write an image
/// `PersistentStore::open` refuses: the same write-accepts / open-refuses trap
/// `initialize_exact_fnsp_v3_state` used to be before `aa09acec7`.
///
/// It calls the production row writer and the production seal advance, and re-derives the faithful
/// leg by READING BACK the durable faithful tables rather than echoing the exact record, so
/// `stage_matching_append_in` still compares two independently reconstructed records. That keeps
/// this a thin harness seam over the production authorities, not a second implementation of them.
///
/// Call it AFTER the exact append is staged in the same writer: the bridge advance validates both
/// durable successor counts.
#[cfg(test)]
pub(crate) fn stage_faithful_counterpart_of_exact_append_in(
    write: &redb::WriteTransaction,
    exact: dregg_circuit::exact_nullifier_aafi::ExactAppendRecord,
) -> Result<()> {
    append_fresh_nullifiers_in(
        write,
        &[FinalizedNullifierRecord {
            nullifier: exact.raw,
            value: exact.value,
        }],
        exact.seq,
    )?;
    let faithful = durable_faithful_exact_append_records_in(write)?
        .last()
        .copied()
        .ok_or_else(|| {
            StoreError::Integrity(
                "faithful counterpart row is absent immediately after it was staged".to_string(),
            )
        })?;
    crate::exact_fnsp_v3_faithful_bridge::stage_matching_append_in(write, faithful, exact)
}

fn require_attested_nullifier_root(
    faithful: &FinalizedFaithfulRootWeld<'_>,
    set: &dregg_cell::nullifier_set::NullifierSet,
) -> Result<()> {
    let expected = set.root8().to_bytes32();
    if faithful.attested_root.nullifier_set_root != Some(expected) {
        return Err(StoreError::Integrity(
            "attested nullifier root does not equal the exact durable successor accumulator"
                .to_string(),
        ));
    }
    Ok(())
}

fn verify_fresh_nullifiers_in(
    write: &redb::WriteTransaction,
    faithful: &FinalizedFaithfulRootWeld<'_>,
) -> Result<u64> {
    if faithful.spent_nullifiers.len() != faithful.finalized_spends.len() {
        return Err(StoreError::Integrity(
            "faithful nullifier records and finalized-spend statements differ in length"
                .to_string(),
        ));
    }
    let mut set = durable_faithful_nullifier_set_in(write)?;
    let first_seq = u64::try_from(set.len()).map_err(|_| {
        StoreError::Integrity("nullifier accumulator length does not fit u64".to_string())
    })?;
    for (spend, statement) in faithful
        .spent_nullifiers
        .iter()
        .zip(faithful.finalized_spends)
    {
        if statement.nullifier != spend.nullifier || statement.value != spend.value {
            return Err(StoreError::Integrity(
                "faithful nullifier record disagrees with finalized-spend statement".to_string(),
            ));
        }
        set.insert(dregg_cell::note::Nullifier(spend.nullifier), spend.value)
            .map_err(|_| {
                StoreError::Integrity(
                    "nullifier already spent or duplicated within finalized turn".to_string(),
                )
            })?;
        if set.root8().to_bytes32() != statement.successor_nullifier_root.to_bytes() {
            return Err(StoreError::Integrity(
                "finalized faithful spend does not bind its exact ordered nullifier successor"
                    .to_string(),
            ));
        }
    }
    require_attested_nullifier_root(faithful, &set)?;
    Ok(first_seq)
}

fn verify_replayed_nullifiers_in(
    write: &redb::WriteTransaction,
    faithful: &FinalizedFaithfulRootWeld<'_>,
) -> Result<()> {
    if faithful.spent_nullifiers.len() != faithful.finalized_spends.len() {
        return Err(StoreError::Integrity(
            "replayed faithful nullifier records and finalized-spend statements differ in length"
                .to_string(),
        ));
    }
    let set = durable_faithful_nullifier_set_in(write)?;
    let records: Vec<_> = set.iter_in_append_order().collect();

    // A no-spend turn carries no sequence coordinate.  Its signed attestation must nevertheless
    // name a genuine durable historical prefix, not an invented root or necessarily the current
    // tail (later finalized turns may have appended more nullifiers before this replay).
    if faithful.spent_nullifiers.is_empty() {
        let claimed = faithful.attested_root.nullifier_set_root.ok_or_else(|| {
            StoreError::Integrity("replayed faithful attestation omits nullifier root".to_string())
        })?;
        let mut prefix = dregg_cell::nullifier_set::NullifierSet::new();
        if prefix.root8().to_bytes32() == claimed {
            return Ok(());
        }
        for (nullifier, value, _) in records {
            prefix.insert(nullifier, value).map_err(|_| {
                StoreError::Integrity(
                    "durable nullifier history cannot reconstruct a replay prefix".to_string(),
                )
            })?;
            if prefix.root8().to_bytes32() == claimed {
                return Ok(());
            }
        }
        return Err(StoreError::Integrity(
            "replayed faithful attestation root is not any durable nullifier prefix".to_string(),
        ));
    }

    let first_nullifier = dregg_cell::note::Nullifier(faithful.spent_nullifiers[0].nullifier);
    let first_seq = set.seq_of(&first_nullifier).ok_or_else(|| {
        StoreError::Integrity("replayed first nullifier is absent from durable history".to_string())
    })?;
    let first_index = usize::try_from(first_seq).map_err(|_| {
        StoreError::Integrity("replayed nullifier sequence does not fit usize".to_string())
    })?;
    let predecessor_records = records.get(..first_index).ok_or_else(|| {
        StoreError::Integrity(
            "replayed nullifier predecessor sequence exceeds durable history".to_string(),
        )
    })?;
    let mut prefix =
        dregg_cell::nullifier_set::NullifierSet::from_records(predecessor_records.iter().copied())
            .map_err(|_| {
                StoreError::Integrity(
                    "replayed nullifier predecessor prefix is malformed".to_string(),
                )
            })?;
    for (offset, (spend, statement)) in faithful
        .spent_nullifiers
        .iter()
        .zip(faithful.finalized_spends)
        .enumerate()
    {
        if statement.nullifier != spend.nullifier || statement.value != spend.value {
            return Err(StoreError::Integrity(
                "replayed faithful nullifier record disagrees with finalized-spend statement"
                    .to_string(),
            ));
        }
        let nullifier = dregg_cell::note::Nullifier(spend.nullifier);
        let expected_seq = first_seq
            .checked_add(u64::try_from(offset).map_err(|_| {
                StoreError::Integrity("replayed nullifier offset does not fit u64".to_string())
            })?)
            .ok_or_else(|| StoreError::Integrity("nullifier sequence overflow".to_string()))?;
        let expected_index = usize::try_from(expected_seq).map_err(|_| {
            StoreError::Integrity("replayed nullifier sequence does not fit usize".to_string())
        })?;
        if records.get(expected_index).copied() != Some((nullifier, spend.value, expected_seq)) {
            return Err(StoreError::Integrity(
                "replayed nullifier/value sequence is not the exact durable historical span"
                    .to_string(),
            ));
        }
        prefix.insert(nullifier, spend.value).map_err(|_| {
            StoreError::Integrity("replayed durable nullifier is duplicated".to_string())
        })?;
        if prefix.root8().to_bytes32() != statement.successor_nullifier_root.to_bytes() {
            return Err(StoreError::Integrity(
                "replayed finalized spend does not bind its historical successor root".to_string(),
            ));
        }
    }
    require_attested_nullifier_root(faithful, &prefix)
}

fn append_fresh_nullifiers_in(
    write: &redb::WriteTransaction,
    spends: &[FinalizedNullifierRecord],
    first_seq: u64,
) -> Result<()> {
    let mut presence = write.open_table(tables::NULLIFIERS)?;
    let mut records = write.open_table(tables::NULLIFIER_RECORDS_V1)?;
    for (offset, spend) in spends.iter().enumerate() {
        if presence.get(&spend.nullifier)?.is_some() || records.get(&spend.nullifier)?.is_some() {
            return Err(StoreError::Integrity(
                "nullifier changed between validation and atomic insertion".to_string(),
            ));
        }
        let seq = first_seq
            .checked_add(u64::try_from(offset).map_err(|_| {
                StoreError::Integrity("nullifier append offset does not fit u64".to_string())
            })?)
            .ok_or_else(|| {
                StoreError::Integrity("nullifier append sequence overflow".to_string())
            })?;
        let encoded = encode_nullifier_record(spend.value, seq);
        presence.insert(&spend.nullifier, ())?;
        records.insert(&spend.nullifier, &encoded)?;
    }
    Ok(())
}

fn durable_note_prefix_in(
    write: &redb::WriteTransaction,
    limit: u64,
    require_exact_len: bool,
) -> Result<Vec<[u8; 32]>> {
    let table = write.open_table(tables::NOTE_COMMITMENTS)?;
    if require_exact_len && table.len()? != limit {
        return Err(StoreError::Integrity(format!(
            "faithful note table length {} differs from sealed note count {limit}",
            table.len()?
        )));
    }
    let limit_usize = usize::try_from(limit).map_err(|_| {
        StoreError::Integrity("faithful note prefix does not fit usize".to_string())
    })?;
    let mut out = Vec::with_capacity(limit_usize);
    for position in 0..limit {
        let commitment = table.get(position)?.ok_or_else(|| {
            StoreError::Integrity(format!(
                "faithful note table has a gap at position {position}"
            ))
        })?;
        out.push(*commitment.value());
    }
    Ok(out)
}

fn verify_faithful_roots_for_prefixes(
    envelope: &FaithfulNoteRootEnvelopeV1,
    predecessor_leaves: &[[u8; 32]],
    successor_leaves: &[[u8; 32]],
) -> Result<()> {
    let predecessor =
        Poseidon2NoteTree::from_blake3_commitments(predecessor_leaves, LIVE_NOTE_TREE_DEPTH)
            .faithful_root_immutable();
    let successor =
        Poseidon2NoteTree::from_blake3_commitments(successor_leaves, LIVE_NOTE_TREE_DEPTH)
            .faithful_root_immutable();
    if crate::CanonicalFaithfulRoot::from_faithful(predecessor) != envelope.record.predecessor
        || crate::CanonicalFaithfulRoot::from_faithful(successor) != envelope.record.successor
    {
        return Err(StoreError::Integrity(
            "faithful note-root edge does not match durable note prefixes".to_string(),
        ));
    }
    Ok(())
}

fn verify_fresh_faithful_notes_in(
    write: &redb::WriteTransaction,
    envelope: &FaithfulNoteRootEnvelopeV1,
    new_commitments: &[[u8; 32]],
    durable_count: u64,
) -> Result<()> {
    let edge = &envelope.record;
    if durable_count != edge.previous_note_count {
        return Err(StoreError::Integrity(format!(
            "faithful predecessor count {} differs from durable note count {durable_count}",
            edge.previous_note_count
        )));
    }
    let added = u64::try_from(new_commitments.len())
        .map_err(|_| StoreError::Integrity("faithful append count does not fit u64".to_string()))?;
    if edge.note_count
        != durable_count
            .checked_add(added)
            .ok_or_else(|| StoreError::Integrity("faithful note count overflow".to_string()))?
    {
        return Err(StoreError::Integrity(
            "faithful successor count does not equal exact append length".to_string(),
        ));
    }
    let predecessor = durable_note_prefix_in(write, durable_count, true)?;
    let mut successor = predecessor.clone();
    successor.extend_from_slice(new_commitments);
    verify_faithful_roots_for_prefixes(envelope, &predecessor, &successor)
}

fn verify_replayed_faithful_notes_in(
    write: &redb::WriteTransaction,
    envelope: &FaithfulNoteRootEnvelopeV1,
    replayed_commitments: &[[u8; 32]],
    durable_count: u64,
) -> Result<()> {
    let edge = &envelope.record;
    if durable_count < edge.note_count {
        return Err(StoreError::Integrity(format!(
            "faithful replay note count {} exceeds durable note count {durable_count}",
            edge.note_count
        )));
    }
    let expected_added = edge
        .note_count
        .checked_sub(edge.previous_note_count)
        .ok_or_else(|| StoreError::Integrity("faithful replay count regressed".to_string()))?;
    if usize::try_from(expected_added).ok() != Some(replayed_commitments.len()) {
        return Err(StoreError::Integrity(
            "faithful replay append length differs from durable edge".to_string(),
        ));
    }
    let successor = durable_note_prefix_in(write, edge.note_count, false)?;
    let predecessor = successor
        .get(
            ..usize::try_from(edge.previous_note_count).map_err(|_| {
                StoreError::Integrity(
                    "faithful replay predecessor count does not fit usize".to_string(),
                )
            })?,
        )
        .ok_or_else(|| {
            StoreError::Integrity("faithful replay predecessor exceeds successor".to_string())
        })?
        .to_vec();
    if successor
        .get(predecessor.len()..)
        .is_none_or(|suffix| suffix != replayed_commitments)
    {
        return Err(StoreError::Integrity(
            "faithful replay note leaves differ from durable edge".to_string(),
        ));
    }
    verify_faithful_roots_for_prefixes(envelope, &predecessor, &successor)
}

impl CommitRecord {
    /// Encode the `(height, creator, ordinal)` composite index key: 8-byte
    /// big-endian height ++ 32-byte creator ++ 8-byte big-endian ordinal.
    /// Big-endian height makes redb's lexicographic order a height-major
    /// order, so range scans are height-ordered. The trailing ordinal makes
    /// the key unique even when several turns commit at the same
    /// `(height, creator)` — which is the normal case for ROUTE-level turns
    /// (trustline/court/channels services), several of which can commit
    /// between two attested-height advances.
    pub fn height_creator_key(height: u64, creator: &[u8; 32], ordinal: u64) -> [u8; 48] {
        let mut key = [0u8; 48];
        key[0..8].copy_from_slice(&height.to_be_bytes());
        key[8..40].copy_from_slice(creator);
        key[40..48].copy_from_slice(&ordinal.to_be_bytes());
        key
    }
}

/// Report from [`PersistentStore::verify_index_agrees_with_log`].
///
/// `ok()` is true exactly when the secondary index is in perfect agreement with
/// the commit log: every record's index entries are present and correct, and the
/// index contains no entries that the log does not justify.
#[derive(Clone, Debug, Default)]
pub struct IndexAuditReport {
    /// Number of commit records physically examined in the (possibly compacted)
    /// log.
    pub records: u64,
    /// `commit_cursor()` value. For a consistent store
    /// `cursor == records + compacted` (the compaction-aware density invariant;
    /// `cursor == records` when nothing has been compacted).
    pub cursor: u64,
    /// `commit_compacted_floor()` value: records compacted away under a covering
    /// checkpoint. The live log holds ordinals `[compacted, cursor)`.
    pub compacted: u64,
    /// Index entries missing for a record that the log contains.
    pub missing_entries: Vec<String>,
    /// Index entries present that no log record justifies (orphans).
    pub orphan_entries: Vec<String>,
    /// Index entries present but pointing at the wrong ordinal.
    pub mismatched_entries: Vec<String>,
}

impl IndexAuditReport {
    /// Whether the index is fully consistent with the log.
    ///
    /// The density check is compaction-aware: `cursor == records + compacted`.
    /// Before any compaction `compacted == 0` and this is the original
    /// `cursor == records`; after compaction the live record count drops by
    /// exactly the compaction floor while the cursor (the applied high-water
    /// mark) is unchanged.
    pub fn ok(&self) -> bool {
        self.cursor == self.records + self.compacted
            && self.missing_entries.is_empty()
            && self.orphan_entries.is_empty()
            && self.mismatched_entries.is_empty()
    }
}

impl PersistentStore {
    // =========================================================================
    // Commit cursor (the crash-consistent recovery anchor)
    // =========================================================================

    /// The durable commit cursor: the number of turns this node has committed
    /// and indexed = the next free commit ordinal = the high-water mark recovery
    /// must resume from. Returns 0 on a fresh node.
    ///
    /// This is read inside the per-turn commit transaction and advanced there, so
    /// it can never be torn against the record it counts.
    pub fn commit_cursor(&self) -> Result<u64> {
        let read_txn = self.db.begin_read()?;
        let meta = read_txn.open_table(tables::METADATA)?;
        Ok(meta
            .get(tables::META_COMMIT_CURSOR)?
            .map(|g| g.value())
            .unwrap_or(0))
    }

    /// Number of records physically present in the commit log table.
    ///
    /// After [`Self::compact_below`] has run, this is strictly less than
    /// [`Self::commit_cursor`] by exactly [`Self::commit_compacted_floor`]:
    /// `commit_cursor() == commit_log_len() + commit_compacted_floor()`.
    pub fn commit_log_len(&self) -> Result<u64> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::COMMIT_LOG)?;
        Ok(table.len()?)
    }

    /// The durable commit-log compaction floor: the number of records compacted
    /// away by [`Self::compact_below`] = the lowest commit ordinal still
    /// physically present in the log. Every ordinal in
    /// `[commit_compacted_floor(), commit_cursor())` resolves to a record;
    /// ordinals below the floor were compacted because a finalized ledger
    /// checkpoint at/above their height subsumes their finalized state. Returns
    /// 0 on a node that has never compacted.
    pub fn commit_compacted_floor(&self) -> Result<u64> {
        let read_txn = self.db.begin_read()?;
        let meta = read_txn.open_table(tables::METADATA)?;
        Ok(meta
            .get(tables::META_COMMIT_COMPACTED)?
            .map(|g| g.value())
            .unwrap_or(0))
    }

    // =========================================================================
    // The atomic commit (single transaction = one fsync boundary)
    // =========================================================================

    /// O(1) live check that the fully audited faithful/exact append-prefix induction still holds.
    ///
    /// Store-open and bootstrap compare both complete histories. Every later production append
    /// advances their shared rolling seal inside the same finalized-turn writer.
    pub fn validate_live_exact_fnsp_v3_faithful_bridge(&self) -> Result<()> {
        let read = self.db.begin_read()?;
        crate::exact_fnsp_v3_faithful_bridge::validate_live_from_read(&read)
    }

    /// Full boot audit (and one-time migration) for the O(1) live bridge.
    pub(crate) fn audit_exact_fnsp_v3_faithful_bridge_on_open(&self) -> Result<()> {
        let write = self.db.begin_write()?;
        let exact_initialized = {
            let heads = write.open_table(crate::exact_fnsp_v3_state::EXACT_FNSP_V3_STATE_HEAD)?;
            heads.len()? != 0
        };
        if exact_initialized {
            validate_exact_fnsp_v3_faithful_prefix_in(&write)?;
        } else {
            crate::exact_fnsp_v3_faithful_bridge::require_absent_in(&write)?;
        }
        write.commit()?;
        Ok(())
    }

    /// Bootstrap the exact FNSP-v3 authority from the complete validated faithful-nullifier image.
    ///
    /// This is the only production seeding path.  Callers supply no records: the store validates
    /// the legacy presence/value/sequence tables inside one writer, derives the exact append image
    /// in dense sequence order, and initializes exact records plus head in that same transaction.
    /// An existing/partial exact authority or a malformed legacy image refuses without mutation.
    pub fn initialize_exact_fnsp_v3_state_from_faithful_nullifiers(
        &self,
    ) -> Result<crate::ExactFnspV3StateHeadV1> {
        let write = self.db.begin_write()?;
        let records = durable_faithful_exact_append_records_in(&write)?;
        let (write, head) = crate::exact_fnsp_v3_state::initialize_exact_fnsp_v3_state_in(
            write,
            records.iter().copied(),
        )?;
        crate::exact_fnsp_v3_faithful_bridge::install_after_full_audit_in(&write, &records)?;
        write.commit()?;
        Ok(head)
    }

    /// Durably commit one finalized turn: append its [`CommitRecord`] at the
    /// current cursor, advance the cursor, and insert all index entries — ALL in
    /// a single redb transaction.
    ///
    /// `expected_ordinal` is the caller's view of the next ordinal (the prior
    /// `executed_up_to`/commit position). It MUST equal the store's current
    /// `commit_cursor`, otherwise the write is refused with an integrity error —
    /// this catches a caller that advanced its in-RAM cursor without durably
    /// committing (the exact torn-state hazard this module exists to remove), and
    /// makes the durable cursor the single source of truth.
    ///
    /// Idempotency: if `expected_ordinal < cursor` AND the record already present
    /// at `expected_ordinal` carries the same `turn_hash`, the call is a no-op
    /// success (a crash-replay re-applying an already-committed turn). Any other
    /// mismatch is an integrity error.
    ///
    /// Returns the ordinal the record was stored at.
    pub fn commit_finalized_turn(
        &self,
        expected_ordinal: u64,
        record: &CommitRecord,
    ) -> Result<u64> {
        self.commit_finalized_turn_with_burns(expected_ordinal, record, &[])
    }

    /// Bare finalized-turn apex with one authoritative PoA Signal transition
    /// welded into the commit-log transaction.  Production federation callers
    /// use the stronger faithful-root/executor-state variants below.
    #[cfg(any(test, feature = "test-support"))]
    pub(crate) fn commit_finalized_turn_with_poa_signal(
        &self,
        expected_ordinal: u64,
        record: &CommitRecord,
        poa_signal: &crate::PreparedPoaSignalTransitionV1,
    ) -> Result<CommitOutcome> {
        self.commit_finalized_turn_welded(
            expected_ordinal,
            record,
            &[],
            &[],
            None,
            None,
            None,
            None,
            &[],
            Some(poa_signal),
            None,
            None,
            None,
        )
        .map(|outcome| outcome.outcome)
    }

    /// Cross-crate fixture apex for restart-audit and atomicity tests only.
    #[cfg(feature = "test-support")]
    #[doc(hidden)]
    pub fn commit_finalized_turn_with_poa_signal_for_test(
        &self,
        expected_ordinal: u64,
        record: &CommitRecord,
        poa_signal: &crate::PreparedPoaSignalTransitionV1,
    ) -> Result<CommitOutcome> {
        self.commit_finalized_turn_with_poa_signal(expected_ordinal, record, poa_signal)
    }

    /// Bare finalized-turn apex with one native-Lean-authored generic PoA event
    /// welded into the commit-log transaction. Rust validates only storage
    /// framing and commit coordinates; game acceptance remains Lean-owned.
    #[cfg(any(test, feature = "test-support"))]
    pub(crate) fn commit_finalized_turn_with_poa_event(
        &self,
        expected_ordinal: u64,
        record: &CommitRecord,
        poa_event: &crate::PreparedPoaEventEnvelopeV1,
    ) -> Result<CommitOutcome> {
        self.commit_finalized_turn_welded(
            expected_ordinal,
            record,
            &[],
            &[],
            None,
            None,
            None,
            None,
            &[],
            None,
            Some(poa_event),
            None,
            None,
        )
        .map(|outcome| outcome.outcome)
    }

    /// Cross-crate fixture apex for legacy V1 event atomicity tests only.
    #[cfg(feature = "test-support")]
    #[doc(hidden)]
    pub fn commit_finalized_turn_with_poa_event_for_test(
        &self,
        expected_ordinal: u64,
        record: &CommitRecord,
        poa_event: &crate::PreparedPoaEventEnvelopeV1,
    ) -> Result<CommitOutcome> {
        self.commit_finalized_turn_with_poa_event(expected_ordinal, record, poa_event)
    }

    /// [`Self::commit_finalized_turn`] PLUS arbitrary config blobs written to
    /// `METADATA_BYTES` in the SAME redb transaction — the same-transaction
    /// CONFIG weld, the general form of the note/burn/receipt welds above.
    ///
    /// # Why this exists
    ///
    /// A caller that must persist a blob ALONGSIDE a commit record had only
    /// [`PersistentStore::set_config`], which opens and commits its OWN write
    /// transaction. Two transactions is two commit-boundary fsyncs for one
    /// logical commit, and on this repo's own durable-World path that was the
    /// entire per-turn cost once the O(N) ledger root was made incremental:
    /// ~10.3 ms per turn, of which ~5 ms was a second fsync of a few hundred
    /// bytes (measured, debug, APFS).
    ///
    /// It also closes a (small) tear: `starbridge_v2::persistence`'s dual-write
    /// stores the replayable input `Turn` under the ordinal the commit is ABOUT
    /// to take and then commits the record. A crash between the two left a turn
    /// blob for an ordinal with no record — harmless there because recovery reads
    /// blobs only below the durable cursor, but it is a window that does not need
    /// to exist. Welded, the blob and the record land together or not at all.
    ///
    /// On an IDEMPOTENT REPLAY of an already-committed turn the blobs are NOT
    /// rewritten, exactly as the welded notes/burns are not: the original commit
    /// wrote them.
    pub fn commit_finalized_turn_with_config(
        &self,
        expected_ordinal: u64,
        record: &CommitRecord,
        config_blobs: &[(&str, &[u8])],
    ) -> Result<u64> {
        self.commit_finalized_turn_welded(
            expected_ordinal,
            record,
            &[],
            &[],
            None,
            None,
            None,
            None,
            config_blobs,
            None,
            None,
            None,
            None,
        )
        .map(|outcome| outcome.outcome.ordinal)
    }

    /// [`Self::commit_finalized_turn`] PLUS note commitments appended to the
    /// Poseidon2 note-tree table in the SAME redb transaction — the
    /// same-transaction NOTE weld.
    ///
    /// # Why this exists (crash-consistency bug #58)
    ///
    /// The node used to append a `NoteCreate` effect's durable commitment in its
    /// OWN redb transaction (`store_note_commitment`), EARLY in the finalized-turn
    /// handler, ~hundreds of lines BEFORE the crash-consistent commit boundary.
    /// A crash after the note append but before [`Self::commit_finalized_turn`]
    /// left the note leaf durable while the turn record was absent from the
    /// commit log — so recovery re-applied the turn and appended the SAME
    /// commitment a SECOND time (two leaves, two positions). Because the boot
    /// path rebuilds the note tree from this table (`load_all_note_commitments`),
    /// the double leaf was PERMANENT and the note-tree root diverged from an
    /// exactly-once peer.
    ///
    /// Welding the note append into the commit transaction closes the window: the
    /// leaf and the turn record land together-or-not-at-all in ONE fsync
    /// boundary. On an idempotent replay of an already-committed turn, the notes
    /// were written by the original commit and are NOT re-appended (the returned
    /// [`CommitOutcome::freshly_committed`] is `false`).
    ///
    /// Positions are assigned sequentially from the current durable note-tree
    /// size, exactly as [`PersistentStore::store_note_commitment`] does; the
    /// cached note-tree root is invalidated within the same transaction.
    pub fn commit_finalized_turn_with_notes(
        &self,
        expected_ordinal: u64,
        record: &CommitRecord,
        note_commitments: &[[u8; 32]],
    ) -> Result<CommitOutcome> {
        self.commit_finalized_turn_welded(
            expected_ordinal,
            record,
            &[],
            note_commitments,
            None,
            None,
            None,
            None,
            &[],
            None,
            None,
            None,
            None,
        )
        .map(|outcome| outcome.outcome)
    }

    /// Commit a turn together with the complete post-execution executor
    /// consensus state. This lower-level entry is useful for non-faithful
    /// callers and restart tests; the live note-root path uses the stronger
    /// faithful-root counterpart below.
    pub fn commit_finalized_turn_with_executor_state(
        &self,
        expected_ordinal: u64,
        record: &CommitRecord,
        note_commitments: &[[u8; 32]],
        executor_state: &crate::FinalizedExecutorConsensusState,
    ) -> Result<CommitOutcome> {
        self.commit_finalized_turn_welded(
            expected_ordinal,
            record,
            &[],
            note_commitments,
            None,
            None,
            None,
            Some(executor_state),
            &[],
            None,
            None,
            None,
            None,
        )
        .map(|outcome| outcome.outcome)
    }

    /// [`Self::commit_finalized_turn_with_notes`] PLUS the exact serialized
    /// `TurnReceipt` at its immutable node-wide log index in the SAME redb
    /// transaction.
    ///
    /// This is the finalized-turn receipt weld: a successful return means the
    /// commit record, note leaves, receipt bytes, and both cursors are durable
    /// together. On idempotent replay, the receipt entry must already exist at
    /// `receipt_index` with byte-identical contents; a missing or conflicting
    /// entry is an integrity error rather than a repaired/shorter history.
    pub fn commit_finalized_turn_with_notes_and_receipt(
        &self,
        expected_ordinal: u64,
        record: &CommitRecord,
        note_commitments: &[[u8; 32]],
        receipt_index: u64,
        encoded_receipt: &[u8],
    ) -> Result<CommitOutcome> {
        self.commit_finalized_turn_welded(
            expected_ordinal,
            record,
            &[],
            note_commitments,
            Some(ReceiptWeldMode::AppendOrVerify {
                index: receipt_index,
                encoded: encoded_receipt,
            }),
            None,
            None,
            None,
            &[],
            None,
            None,
            None,
            None,
        )
        .map(|outcome| outcome.outcome)
    }

    /// The live faithful-root apex: commit record, exact note leaves, receipt,
    /// hybrid-authenticated faithful history edge, exact-root attestation, and
    /// every cursor in one redb transaction.
    ///
    /// The store independently reconstructs predecessor and successor roots
    /// from its durable positional note table.  A caller cannot pair a validly
    /// signed but unrelated root edge with different leaves, or publish the old
    /// one-felt alias as the live attestation root.
    #[allow(clippy::too_many_arguments)]
    pub fn commit_finalized_turn_with_faithful_root(
        &self,
        expected_ordinal: u64,
        record: &CommitRecord,
        note_commitments: &[[u8; 32]],
        receipt_index: u64,
        encoded_receipt: &[u8],
        faithful: FinalizedFaithfulRootWeld<'_>,
    ) -> Result<CommitOutcome> {
        self.commit_finalized_turn_with_faithful_root_receipt_mode(
            expected_ordinal,
            record,
            note_commitments,
            ReceiptWeldMode::AppendOrVerify {
                index: receipt_index,
                encoded: encoded_receipt,
            },
            faithful,
            None,
            None,
            None,
        )
    }

    /// The live faithful-root apex plus the complete post-execution consensus
    /// accumulator image and canonical rate-limit snapshot. The side state is
    /// validated as an exact extension and lands in the same redb transaction
    /// as the record, receipt, roots, and commit cursor.
    #[allow(clippy::too_many_arguments)]
    pub fn commit_finalized_turn_with_faithful_root_and_executor_state(
        &self,
        expected_ordinal: u64,
        record: &CommitRecord,
        note_commitments: &[[u8; 32]],
        receipt_index: u64,
        encoded_receipt: &[u8],
        faithful: FinalizedFaithfulRootWeld<'_>,
        executor_state: &crate::FinalizedExecutorConsensusState,
    ) -> Result<CommitOutcome> {
        self.commit_finalized_turn_with_faithful_root_receipt_mode(
            expected_ordinal,
            record,
            note_commitments,
            ReceiptWeldMode::AppendOrVerify {
                index: receipt_index,
                encoded: encoded_receipt,
            },
            faithful,
            None,
            Some(executor_state),
            None,
        )
    }

    /// Faithful/executor-state finalized apex with one authoritative PoA Signal
    /// transition welded into the same redb transaction.
    #[allow(clippy::too_many_arguments)]
    pub fn commit_finalized_turn_with_faithful_root_and_executor_state_and_poa_signal(
        &self,
        expected_ordinal: u64,
        record: &CommitRecord,
        note_commitments: &[[u8; 32]],
        receipt_index: u64,
        encoded_receipt: &[u8],
        faithful: FinalizedFaithfulRootWeld<'_>,
        executor_state: &crate::FinalizedExecutorConsensusState,
        poa_signal: &crate::PreparedPoaSignalTransitionV1,
    ) -> Result<CommitOutcome> {
        self.commit_finalized_turn_with_faithful_root_receipt_mode(
            expected_ordinal,
            record,
            note_commitments,
            ReceiptWeldMode::AppendOrVerify {
                index: receipt_index,
                encoded: encoded_receipt,
            },
            faithful,
            None,
            Some(executor_state),
            Some(poa_signal),
        )
    }

    /// Faithful/executor-state finalized apex with one legacy Lean-authored PoA
    /// V1 event. V1 has no receipt-bound signer coordinate, so this public apex
    /// is intentionally public-play only. Holder mechanics use the V2 batch
    /// apex, whose authority weld can bind player and cell to the receipt.
    #[allow(clippy::too_many_arguments)]
    pub fn commit_finalized_turn_with_faithful_root_and_executor_state_and_poa_event(
        &self,
        expected_ordinal: u64,
        record: &CommitRecord,
        note_commitments: &[[u8; 32]],
        receipt_index: u64,
        encoded_receipt: &[u8],
        faithful: FinalizedFaithfulRootWeld<'_>,
        executor_state: &crate::FinalizedExecutorConsensusState,
        poa_event: &crate::PreparedPoaEventEnvelopeV1,
    ) -> Result<CommitOutcome> {
        self.commit_finalized_turn_with_faithful_root_receipt_mode_with_poa(
            expected_ordinal,
            record,
            note_commitments,
            ReceiptWeldMode::AppendOrVerify {
                index: receipt_index,
                encoded: encoded_receipt,
            },
            faithful,
            None,
            Some(executor_state),
            None,
            Some(poa_event),
            None,
            None,
        )
    }

    /// Faithful/executor-state finalized apex with an ordered PoA V2 event
    /// batch and optional one-shot holding-capability consumption. The exact
    /// receipt, ordered batch manifest, all event/projection edges, and the
    /// capability nullifier land or fail in the same redb transaction.
    #[allow(clippy::too_many_arguments)]
    pub fn commit_finalized_turn_with_faithful_root_and_executor_state_and_poa_event_batch(
        &self,
        expected_ordinal: u64,
        record: &CommitRecord,
        note_commitments: &[[u8; 32]],
        receipt_index: u64,
        encoded_receipt: &[u8],
        faithful: FinalizedFaithfulRootWeld<'_>,
        executor_state: &crate::FinalizedExecutorConsensusState,
        poa_batch: &crate::PreparedPoaEventBatchV2,
        poa_holding: Option<&crate::PreparedPoaHoldingConsumptionV1>,
    ) -> Result<CommitOutcome> {
        self.commit_finalized_turn_with_faithful_root_receipt_mode_with_poa(
            expected_ordinal,
            record,
            note_commitments,
            ReceiptWeldMode::AppendOrVerify {
                index: receipt_index,
                encoded: encoded_receipt,
            },
            faithful,
            None,
            Some(executor_state),
            None,
            None,
            Some(poa_batch),
            poa_holding,
        )
    }

    /// Commit one sealed Galley transition at the finalized-turn apex.
    ///
    /// This crate-private Galley durability adapter consumes the opaque carrier
    /// produced by the persistence-owned Galley authority braid;
    /// callers never receive or supply its inner `PreparedPoaEventBatchV2`.
    /// The existing central writer remains the single semantic path:
    ///
    /// * a fresh turn re-audits the exact current signed world under the same
    ///   redb writer, then applies the durable stream-head CAS before commit;
    /// * an idempotent retry re-audits the batch's historical signed-world
    ///   prefix and requires the stored manifest/event bytes to be exact; and
    /// * the generic receipt, faithful/executor state, event journal, and heads
    ///   commit together or the sole writer is dropped without mutation.
    ///
    /// `PreparedPoaGalleyEventBatchV1` is cloneable only so a caller can retain
    /// the exact sealed retry carrier across an uncertain commit response.  It
    /// exposes no constructor or inner-batch accessor outside this crate.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn commit_finalized_turn_with_faithful_root_and_executor_state_and_poa_galley(
        &self,
        expected_ordinal: u64,
        record: &CommitRecord,
        note_commitments: &[[u8; 32]],
        receipt_index: u64,
        encoded_receipt: &[u8],
        faithful: FinalizedFaithfulRootWeld<'_>,
        executor_state: &crate::FinalizedExecutorConsensusState,
        poa_galley: crate::PreparedPoaGalleyEventBatchV1,
    ) -> Result<CommitOutcome> {
        let poa_batch = poa_galley.into_event_batch();
        self.commit_finalized_turn_with_faithful_root_and_executor_state_and_poa_event_batch(
            expected_ordinal,
            record,
            note_commitments,
            receipt_index,
            encoded_receipt,
            faithful,
            executor_state,
            &poa_batch,
            None,
        )
    }

    /// Production Galley public-play apex.
    ///
    /// The caller supplies the genuine lower `SignedTurn` and `TurnReceipt`,
    /// plus the same faithful/executor welds required by every finalized turn.
    /// It cannot supply a policy, world, action token, prepared finality, or
    /// EventBatch. Those are derived only after the central writer has staged
    /// and rechecked the exact finalized receipt and consensus projections.
    #[allow(clippy::too_many_arguments)]
    pub fn commit_finalized_poa_galley_public_perform_v1(
        &self,
        expected_ordinal: u64,
        record: &CommitRecord,
        note_commitments: &[[u8; 32]],
        receipt_index: u64,
        signed_turn: &dregg_turn::SignedTurn,
        receipt: &dregg_turn::TurnReceipt,
        faithful: FinalizedFaithfulRootWeld<'_>,
        executor_state: &crate::FinalizedExecutorConsensusState,
    ) -> Result<CommitOutcome> {
        if !faithful.envelope.verify_hybrid(
            faithful.author_committee,
            faithful.author_ml_dsa_committee,
            1,
        ) {
            return Err(StoreError::Integrity(
                "faithful note-root author hybrid signature failed".to_string(),
            ));
        }
        if !faithful.attested_root.has_any_valid_committee_signature(
            faithful.author_committee,
            faithful.author_ml_dsa_committee,
        ) {
            return Err(StoreError::Integrity(
                "faithful note-root attestation has no valid author signature".to_string(),
            ));
        }
        validate_faithful_commit_coordinates(record, &faithful)?;
        let encoded_receipt = postcard::to_stdvec(receipt)
            .map_err(|error| StoreError::Serialization(error.to_string()))?;
        if receipt.receipt_hash() != record.receipt_hash {
            return Err(StoreError::Integrity(
                "Galley raw receipt hash disagrees with carrying commit".to_string(),
            ));
        }
        self.commit_finalized_turn_welded_with_raw_galley(
            expected_ordinal,
            record,
            &[],
            note_commitments,
            Some(ReceiptWeldMode::AppendOrVerify {
                index: receipt_index,
                encoded: &encoded_receipt,
            }),
            Some(faithful),
            None,
            Some(executor_state),
            &[],
            None,
            None,
            None,
            None,
            Some(PoaGalleyRawWeld {
                signed_turn,
                receipt,
            }),
        )
        .map(|outcome| outcome.outcome)
    }

    /// The faithful-root apex plus the exact FNSP-v3 durable append/head CAS.
    ///
    /// This is the transaction-owned promotion substrate: the candidate must name the turn's one
    /// finalized `(nullifier, value)`, is independently replayed against the durable exact prefix,
    /// and is inserted only after every other fallible finalized-turn write has been staged.  The
    /// consuming CAS returns the same writer only on total success; a stale or forged candidate
    /// therefore aborts the commit record, receipt, leaves, root history, attestation, legacy
    /// nullifier rows, finalized-spend authority, and cursor together.
    ///
    /// Predicate registration remains a separate fail-closed cut: callers must not use this
    /// persistence method as evidence that an exact-v3 proof identity was accepted.
    #[allow(clippy::too_many_arguments)]
    #[cfg(test)]
    pub(crate) fn commit_finalized_turn_with_faithful_root_and_exact_fnsp_v3(
        &self,
        expected_ordinal: u64,
        record: &CommitRecord,
        note_commitments: &[[u8; 32]],
        receipt_index: u64,
        encoded_receipt: &[u8],
        faithful: FinalizedFaithfulRootWeld<'_>,
        exact: crate::ExactFnspV3StateCasV1,
    ) -> Result<CommitOutcome> {
        self.commit_finalized_turn_with_faithful_root_receipt_mode(
            expected_ordinal,
            record,
            note_commitments,
            ReceiptWeldMode::AppendOrVerify {
                index: receipt_index,
                encoded: encoded_receipt,
            },
            faithful,
            Some(ExactFnspV3Weld::AccumulatorOnly(exact)),
            None,
            None,
        )
    }

    /// Production exact-v3 apex: the executor-produced receipt, faithful state, exact append, and
    /// restart-safe signed frame record/head land under one writer transaction.
    #[allow(clippy::too_many_arguments)]
    pub fn commit_finalized_turn_with_faithful_root_and_exact_fnsp_v3_frame(
        &self,
        expected_ordinal: u64,
        record: &CommitRecord,
        receipt_index: u64,
        encoded_receipt: &[u8],
        faithful: FinalizedFaithfulRootWeld<'_>,
        exact: crate::ExactFnspV3StateCasV1,
        frame: crate::UntrustedExactFnspV3FrameV1,
        activation: Option<crate::UntrustedExactFnspV3ActivationV1>,
        executor_state: &crate::FinalizedExecutorConsensusState,
    ) -> Result<ExactFnspV3FrameCommitOutcome> {
        self.commit_finalized_turn_with_exact_fnsp_v3_frame_receipt_mode(
            expected_ordinal,
            record,
            ReceiptWeldMode::AppendOrVerify {
                index: receipt_index,
                encoded: encoded_receipt,
            },
            faithful,
            exact,
            frame,
            activation,
            executor_state,
        )
    }

    /// [`Self::commit_finalized_turn_with_faithful_root`] for the solo-finality
    /// custody case where ingress already durably appended the exact receipt.
    ///
    /// The receipt row is verified byte-for-byte inside the carrying redb
    /// transaction but may never be inserted by it. A missing tail row,
    /// conflicting older row, or non-dense log aborts the entire faithful commit
    /// without advancing the commit cursor, note/nullifier frontier, root
    /// history, or attestation. The durable receipt-log length is therefore
    /// unchanged on both success and failure.
    #[allow(clippy::too_many_arguments)]
    pub fn commit_finalized_turn_with_faithful_root_existing_receipt(
        &self,
        expected_ordinal: u64,
        record: &CommitRecord,
        note_commitments: &[[u8; 32]],
        receipt_index: u64,
        encoded_receipt: &[u8],
        faithful: FinalizedFaithfulRootWeld<'_>,
    ) -> Result<CommitOutcome> {
        self.commit_finalized_turn_with_faithful_root_receipt_mode(
            expected_ordinal,
            record,
            note_commitments,
            ReceiptWeldMode::ExistingExact {
                index: receipt_index,
                encoded: encoded_receipt,
            },
            faithful,
            None,
            None,
            None,
        )
    }

    /// Existing-receipt counterpart of
    /// [`Self::commit_finalized_turn_with_faithful_root_and_executor_state`].
    #[allow(clippy::too_many_arguments)]
    pub fn commit_finalized_turn_with_faithful_root_and_executor_state_existing_receipt(
        &self,
        expected_ordinal: u64,
        record: &CommitRecord,
        note_commitments: &[[u8; 32]],
        receipt_index: u64,
        encoded_receipt: &[u8],
        faithful: FinalizedFaithfulRootWeld<'_>,
        executor_state: &crate::FinalizedExecutorConsensusState,
    ) -> Result<CommitOutcome> {
        self.commit_finalized_turn_with_faithful_root_receipt_mode(
            expected_ordinal,
            record,
            note_commitments,
            ReceiptWeldMode::ExistingExact {
                index: receipt_index,
                encoded: encoded_receipt,
            },
            faithful,
            None,
            Some(executor_state),
            None,
        )
    }

    /// Existing-receipt counterpart of the faithful/executor-state PoA Signal
    /// apex.  The receipt and Signal transition must both already be exact on
    /// idempotent replay; neither may be repaired or omitted.
    #[allow(clippy::too_many_arguments)]
    pub fn commit_finalized_turn_with_faithful_root_and_executor_state_existing_receipt_and_poa_signal(
        &self,
        expected_ordinal: u64,
        record: &CommitRecord,
        note_commitments: &[[u8; 32]],
        receipt_index: u64,
        encoded_receipt: &[u8],
        faithful: FinalizedFaithfulRootWeld<'_>,
        executor_state: &crate::FinalizedExecutorConsensusState,
        poa_signal: &crate::PreparedPoaSignalTransitionV1,
    ) -> Result<CommitOutcome> {
        self.commit_finalized_turn_with_faithful_root_receipt_mode(
            expected_ordinal,
            record,
            note_commitments,
            ReceiptWeldMode::ExistingExact {
                index: receipt_index,
                encoded: encoded_receipt,
            },
            faithful,
            None,
            Some(executor_state),
            Some(poa_signal),
        )
    }

    /// Existing-receipt crash-replay counterpart of the legacy public-play PoA
    /// V1 event apex. Replay requires the byte-identical event; V1 never admits
    /// holding consumption because it cannot bind a signer to the receipt.
    #[allow(clippy::too_many_arguments)]
    pub fn commit_finalized_turn_with_faithful_root_and_executor_state_existing_receipt_and_poa_event(
        &self,
        expected_ordinal: u64,
        record: &CommitRecord,
        note_commitments: &[[u8; 32]],
        receipt_index: u64,
        encoded_receipt: &[u8],
        faithful: FinalizedFaithfulRootWeld<'_>,
        executor_state: &crate::FinalizedExecutorConsensusState,
        poa_event: &crate::PreparedPoaEventEnvelopeV1,
    ) -> Result<CommitOutcome> {
        self.commit_finalized_turn_with_faithful_root_receipt_mode_with_poa(
            expected_ordinal,
            record,
            note_commitments,
            ReceiptWeldMode::ExistingExact {
                index: receipt_index,
                encoded: encoded_receipt,
            },
            faithful,
            None,
            Some(executor_state),
            None,
            Some(poa_event),
            None,
            None,
        )
    }

    /// Existing-receipt crash-replay counterpart of the faithful PoA V2 batch
    /// apex. Replay requires the byte-identical ordered batch manifest and
    /// optional holding-consumption weld; omission and invention both refuse.
    #[allow(clippy::too_many_arguments)]
    pub fn commit_finalized_turn_with_faithful_root_and_executor_state_existing_receipt_and_poa_event_batch(
        &self,
        expected_ordinal: u64,
        record: &CommitRecord,
        note_commitments: &[[u8; 32]],
        receipt_index: u64,
        encoded_receipt: &[u8],
        faithful: FinalizedFaithfulRootWeld<'_>,
        executor_state: &crate::FinalizedExecutorConsensusState,
        poa_batch: &crate::PreparedPoaEventBatchV2,
        poa_holding: Option<&crate::PreparedPoaHoldingConsumptionV1>,
    ) -> Result<CommitOutcome> {
        self.commit_finalized_turn_with_faithful_root_receipt_mode_with_poa(
            expected_ordinal,
            record,
            note_commitments,
            ReceiptWeldMode::ExistingExact {
                index: receipt_index,
                encoded: encoded_receipt,
            },
            faithful,
            None,
            Some(executor_state),
            None,
            None,
            Some(poa_batch),
            poa_holding,
        )
    }

    /// Exact-FNSP-v3 counterpart of
    /// [`Self::commit_finalized_turn_with_faithful_root_existing_receipt`].
    /// The receipt must already exist byte-for-byte; this method never repairs or appends it.
    #[allow(clippy::too_many_arguments)]
    #[cfg(test)]
    pub(crate) fn commit_finalized_turn_with_faithful_root_and_exact_fnsp_v3_existing_receipt(
        &self,
        expected_ordinal: u64,
        record: &CommitRecord,
        note_commitments: &[[u8; 32]],
        receipt_index: u64,
        encoded_receipt: &[u8],
        faithful: FinalizedFaithfulRootWeld<'_>,
        exact: crate::ExactFnspV3StateCasV1,
    ) -> Result<CommitOutcome> {
        self.commit_finalized_turn_with_faithful_root_receipt_mode(
            expected_ordinal,
            record,
            note_commitments,
            ReceiptWeldMode::ExistingExact {
                index: receipt_index,
                encoded: encoded_receipt,
            },
            faithful,
            Some(ExactFnspV3Weld::AccumulatorOnly(exact)),
            None,
            None,
        )
    }

    /// Crash-replay counterpart of
    /// [`Self::commit_finalized_turn_with_faithful_root_and_exact_fnsp_v3_frame`].
    #[allow(clippy::too_many_arguments)]
    pub fn commit_finalized_turn_with_faithful_root_and_exact_fnsp_v3_frame_existing_receipt(
        &self,
        expected_ordinal: u64,
        record: &CommitRecord,
        receipt_index: u64,
        encoded_receipt: &[u8],
        faithful: FinalizedFaithfulRootWeld<'_>,
        exact: crate::ExactFnspV3StateCasV1,
        frame: crate::UntrustedExactFnspV3FrameV1,
        activation: Option<crate::UntrustedExactFnspV3ActivationV1>,
        executor_state: &crate::FinalizedExecutorConsensusState,
    ) -> Result<ExactFnspV3FrameCommitOutcome> {
        self.commit_finalized_turn_with_exact_fnsp_v3_frame_receipt_mode(
            expected_ordinal,
            record,
            ReceiptWeldMode::ExistingExact {
                index: receipt_index,
                encoded: encoded_receipt,
            },
            faithful,
            exact,
            frame,
            activation,
            executor_state,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn commit_finalized_turn_with_exact_fnsp_v3_frame_receipt_mode(
        &self,
        expected_ordinal: u64,
        record: &CommitRecord,
        receipt_entry: ReceiptWeldMode<'_>,
        faithful: FinalizedFaithfulRootWeld<'_>,
        exact: crate::ExactFnspV3StateCasV1,
        frame: crate::UntrustedExactFnspV3FrameV1,
        activation: Option<crate::UntrustedExactFnspV3ActivationV1>,
        executor_state: &crate::FinalizedExecutorConsensusState,
    ) -> Result<ExactFnspV3FrameCommitOutcome> {
        if !faithful.envelope.verify_hybrid(
            faithful.author_committee,
            faithful.author_ml_dsa_committee,
            1,
        ) {
            return Err(StoreError::Integrity(
                "faithful note-root author hybrid signature failed".to_string(),
            ));
        }
        if !faithful.attested_root.has_any_valid_committee_signature(
            faithful.author_committee,
            faithful.author_ml_dsa_committee,
        ) {
            return Err(StoreError::Integrity(
                "faithful note-root attestation has no valid author signature".to_string(),
            ));
        }
        validate_faithful_commit_coordinates(record, &faithful)?;
        validate_exact_fnsp_v3_finalization_coordinates(&faithful, exact)?;
        let welded = self.commit_finalized_turn_welded(
            expected_ordinal,
            record,
            &[],
            &[],
            Some(receipt_entry),
            Some(faithful),
            Some(ExactFnspV3Weld::Frame {
                exact,
                activation,
                frame,
            }),
            Some(executor_state),
            &[],
            None,
            None,
            None,
            None,
        )?;
        let committed_head = welded.committed_head.ok_or_else(|| {
            StoreError::Integrity(
                "exact FNSP-v3 frame commit returned without a committed head".to_string(),
            )
        })?;
        Ok(ExactFnspV3FrameCommitOutcome {
            outcome: welded.outcome,
            committed_head,
            finalized_receipt_core_id: welded.finalized_receipt_core_id.ok_or_else(|| {
                StoreError::Integrity(
                    "exact FNSP-v3 frame commit returned without a finalized receipt core id"
                        .to_string(),
                )
            })?,
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn commit_finalized_turn_with_faithful_root_receipt_mode(
        &self,
        expected_ordinal: u64,
        record: &CommitRecord,
        note_commitments: &[[u8; 32]],
        receipt_entry: ReceiptWeldMode<'_>,
        faithful: FinalizedFaithfulRootWeld<'_>,
        exact_fnsp_v3: Option<ExactFnspV3Weld>,
        executor_state: Option<&crate::FinalizedExecutorConsensusState>,
        poa_signal: Option<&crate::PreparedPoaSignalTransitionV1>,
    ) -> Result<CommitOutcome> {
        self.commit_finalized_turn_with_faithful_root_receipt_mode_with_poa(
            expected_ordinal,
            record,
            note_commitments,
            receipt_entry,
            faithful,
            exact_fnsp_v3,
            executor_state,
            poa_signal,
            None,
            None,
            None,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn commit_finalized_turn_with_faithful_root_receipt_mode_with_poa(
        &self,
        expected_ordinal: u64,
        record: &CommitRecord,
        note_commitments: &[[u8; 32]],
        receipt_entry: ReceiptWeldMode<'_>,
        faithful: FinalizedFaithfulRootWeld<'_>,
        exact_fnsp_v3: Option<ExactFnspV3Weld>,
        executor_state: Option<&crate::FinalizedExecutorConsensusState>,
        poa_signal: Option<&crate::PreparedPoaSignalTransitionV1>,
        poa_event: Option<&crate::PreparedPoaEventEnvelopeV1>,
        poa_batch: Option<&crate::PreparedPoaEventBatchV2>,
        poa_holding: Option<&crate::PreparedPoaHoldingConsumptionV1>,
    ) -> Result<CommitOutcome> {
        if !faithful.envelope.verify_hybrid(
            faithful.author_committee,
            faithful.author_ml_dsa_committee,
            1,
        ) {
            return Err(StoreError::Integrity(
                "faithful note-root author hybrid signature failed".to_string(),
            ));
        }
        if !faithful.attested_root.has_any_valid_committee_signature(
            faithful.author_committee,
            faithful.author_ml_dsa_committee,
        ) {
            return Err(StoreError::Integrity(
                "faithful note-root attestation has no valid author signature".to_string(),
            ));
        }
        validate_faithful_commit_coordinates(record, &faithful)?;
        if let Some(exact) = exact_fnsp_v3.as_ref() {
            validate_exact_fnsp_v3_finalization_coordinates(&faithful, exact.exact())?;
        }
        self.commit_finalized_turn_welded(
            expected_ordinal,
            record,
            &[],
            note_commitments,
            Some(receipt_entry),
            Some(faithful),
            exact_fnsp_v3,
            executor_state,
            &[],
            poa_signal,
            poa_event,
            poa_batch,
            poa_holding,
        )
        .map(|outcome| outcome.outcome)
    }

    /// [`Self::commit_finalized_turn`] PLUS forever-digest burns in the SAME
    /// redb transaction — the same-transaction burn weld (.docs-history-noclaude/PERSISTENCE.md
    /// §3): a turn that burns an anti-replay digest (a trustline draw, a court
    /// slash) lands its commit record AND its digest atomically, so no crash
    /// can leave the turn durable without its burn or the burn durable without
    /// its turn. Each burn is `(namespace, scope, digest)` exactly as
    /// [`PersistentStore::record_forever_digest`] takes them.
    ///
    /// On an idempotent replay (the record at `expected_ordinal` already holds
    /// the same `turn_hash`), the burns were already written by the original
    /// commit and the call is a no-op success.
    pub fn commit_finalized_turn_with_burns(
        &self,
        expected_ordinal: u64,
        record: &CommitRecord,
        burns: &[(u8, [u8; 32], [u8; 32])],
    ) -> Result<u64> {
        self.commit_finalized_turn_welded(
            expected_ordinal,
            record,
            burns,
            &[],
            None,
            None,
            None,
            None,
            &[],
            None,
            None,
            None,
            None,
        )
        .map(|outcome| outcome.outcome.ordinal)
    }

    /// The single atomic finalized-turn commit: record + secondary index +
    /// forever-digest burns + note-tree leaves + cursor advance, all in ONE redb
    /// transaction (one fsync boundary). Every public commit entry point routes
    /// here; the burn and note welds keep those side-effects exactly-once with
    /// the turn record across an arbitrary crash. Returns a [`CommitOutcome`]
    /// distinguishing a fresh write from an idempotent replay.
    fn commit_finalized_turn_welded(
        &self,
        expected_ordinal: u64,
        record: &CommitRecord,
        burns: &[(u8, [u8; 32], [u8; 32])],
        note_commitments: &[[u8; 32]],
        receipt_entry: Option<ReceiptWeldMode<'_>>,
        faithful: Option<FinalizedFaithfulRootWeld<'_>>,
        exact_fnsp_v3: Option<ExactFnspV3Weld>,
        executor_state: Option<&crate::FinalizedExecutorConsensusState>,
        config_blobs: &[(&str, &[u8])],
        poa_signal: Option<&crate::PreparedPoaSignalTransitionV1>,
        poa_event: Option<&crate::PreparedPoaEventEnvelopeV1>,
        poa_batch: Option<&crate::PreparedPoaEventBatchV2>,
        poa_holding: Option<&crate::PreparedPoaHoldingConsumptionV1>,
    ) -> Result<WeldedCommitOutcome> {
        self.commit_finalized_turn_welded_with_raw_galley(
            expected_ordinal,
            record,
            burns,
            note_commitments,
            receipt_entry,
            faithful,
            exact_fnsp_v3,
            executor_state,
            config_blobs,
            poa_signal,
            poa_event,
            poa_batch,
            poa_holding,
            None,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn commit_finalized_turn_welded_with_raw_galley(
        &self,
        expected_ordinal: u64,
        record: &CommitRecord,
        burns: &[(u8, [u8; 32], [u8; 32])],
        note_commitments: &[[u8; 32]],
        receipt_entry: Option<ReceiptWeldMode<'_>>,
        faithful: Option<FinalizedFaithfulRootWeld<'_>>,
        exact_fnsp_v3: Option<ExactFnspV3Weld>,
        executor_state: Option<&crate::FinalizedExecutorConsensusState>,
        config_blobs: &[(&str, &[u8])],
        poa_signal: Option<&crate::PreparedPoaSignalTransitionV1>,
        poa_event: Option<&crate::PreparedPoaEventEnvelopeV1>,
        poa_batch: Option<&crate::PreparedPoaEventBatchV2>,
        poa_holding: Option<&crate::PreparedPoaHoldingConsumptionV1>,
        poa_galley: Option<PoaGalleyRawWeld<'_>>,
    ) -> Result<WeldedCommitOutcome> {
        if poa_galley.is_some()
            && (poa_signal.is_some()
                || poa_event.is_some()
                || poa_batch.is_some()
                || poa_holding.is_some())
        {
            return Err(StoreError::Integrity(
                "raw Galley finalization cannot be combined with caller-prepared PoA welds"
                    .to_string(),
            ));
        }
        if poa_event.is_some() && poa_batch.is_some() {
            return Err(StoreError::Integrity(
                "finalized turn cannot weld both a PoA V1 event and V2 event batch".to_string(),
            ));
        }
        if let Some(batch) = poa_batch {
            let receipt_entry = receipt_entry.as_ref().ok_or_else(|| {
                StoreError::Integrity(
                    "PoA V2 batch requires the exact finalized receipt at the atomic apex"
                        .to_string(),
                )
            })?;
            let (_, encoded_receipt) = receipt_entry.entry();
            validate_poa_v2_batch_authority(record, encoded_receipt, batch, poa_holding)?;
        }
        match (poa_holding, poa_event, poa_batch) {
            (Some(holding), Some(event), None) if holding.matches_poa_event(event) => {}
            (Some(holding), None, Some(batch)) if holding.matches_poa_batch(batch) => {}
            (Some(_), Some(_), None) | (Some(_), None, Some(_)) => {
                return Err(StoreError::Integrity(
                    "PoA holding consumption is not bound to one exact welded PoA event"
                        .to_string(),
                ));
            }
            (Some(_), None, None) => {
                return Err(StoreError::Integrity(
                    "PoA holding consumption requires an exact welded PoA event".to_string(),
                ));
            }
            (None, _, _) => {}
            (Some(_), Some(_), Some(_)) => unreachable!("both world welds refused above"),
        }
        let write_txn = self.db.begin_write()?;
        // Store-open/bootstrap established full faithful/exact history equality. The rolling
        // bridge is its durable induction hypothesis, so live admission checks only sealed count +
        // exact head instead of replaying both O(N) histories on every turn.
        if exact_fnsp_v3.is_some() {
            crate::exact_fnsp_v3_faithful_bridge::validate_live_from_write(&write_txn)?;
        }
        let exact_bridge_append = exact_fnsp_v3
            .as_ref()
            .map(|weld| weld.exact().append_record());
        let mut faithful_bridge_append = None;
        let mut finalized_receipt_core_id = None;
        let assigned;
        {
            let mut meta = write_txn.open_table(tables::METADATA)?;
            let cursor = meta
                .get(tables::META_COMMIT_CURSOR)?
                .map(|g| g.value())
                .unwrap_or(0);

            if expected_ordinal != cursor {
                // Idempotent replay: the caller is re-applying a turn we already
                // committed durably. Accept iff the stored record matches.
                if expected_ordinal < cursor {
                    let log = write_txn.open_table(tables::COMMIT_LOG)?;
                    let existing = match log.get(expected_ordinal)? {
                        Some(guard) => decode_commit_record(guard.value())?,
                        None => {
                            let compacted_floor = meta
                                .get(tables::META_COMMIT_COMPACTED)?
                                .map(|value| value.value())
                                .unwrap_or(0);
                            if expected_ordinal >= compacted_floor {
                                return Err(StoreError::Integrity(format!(
                                    "commit_finalized_turn: cursor {cursor} > expected {expected_ordinal} \
                                     but no live or compacted authority at that ordinal (corrupt log)"
                                )));
                            }
                            crate::poa_compact_authority::require_exact_compacted_record_in(
                                &write_txn,
                                compacted_floor,
                                expected_ordinal,
                                record,
                            )?;
                            record.clone()
                        }
                    };
                    drop(log);
                    if existing.turn_hash == record.turn_hash {
                        let durable_note_count = meta
                            .get(tables::META_NOTE_TREE_SIZE)?
                            .map(|guard| guard.value())
                            .unwrap_or(0);
                        let tracked_executor_state = {
                            let frontiers =
                                write_txn.open_table(tables::EXECUTOR_ACCUMULATOR_FRONTIERS_V1)?;
                            frontiers.get(expected_ordinal)?.is_some()
                        };
                        match (executor_state, tracked_executor_state) {
                            (Some(state), true) => {
                                crate::executor_consensus_state::verify_replayed_executor_consensus_state_in(
                                            &write_txn,
                                            expected_ordinal,
                                            durable_note_count,
                                            note_commitments,
                                            state,
                                        )?;
                                crate::promise_resolutions::verify_replayed_promise_resolution_batch_in(
                                            &write_txn,
                                            &existing,
                                            &state.promise_resolutions,
                                        )?;
                            }
                            (None, false) => {}
                            _ => {
                                return Err(StoreError::Integrity(
                                            "replayed finalized turn omitted or invented its executor consensus-state weld"
                                                .to_string(),
                                        ));
                            }
                        }
                        crate::poa_signal_state::verify_replayed_poa_signal_transition_in(
                            &write_txn,
                            expected_ordinal,
                            &existing,
                            poa_signal,
                        )?;
                        crate::poa_event_store::verify_replayed_poa_event_in(
                            &write_txn,
                            expected_ordinal,
                            &existing,
                            poa_event,
                        )?;
                        if poa_galley.is_none() {
                            if let Some(poa_batch) = poa_batch {
                                crate::poa_world_activation::require_poa_historical_world_exact_in(
                                    &write_txn,
                                    poa_batch.coordinate().world(),
                                )?;
                            }
                            crate::poa_event_batch_v2::verify_replayed_poa_event_batch_in(
                                &write_txn,
                                expected_ordinal,
                                &existing,
                                poa_batch,
                            )?;
                            crate::poa_holding_consumption::verify_replayed_poa_holding_consumption_in(
                                        &write_txn,
                                        expected_ordinal,
                                        &existing,
                                        poa_holding,
                                    )?;
                        }
                        crate::per_cell_receipt_heads::verify_replayed_per_cell_receipt_heads_in(
                            &write_txn, &existing,
                        )?;
                        if let Some(receipt_entry) = receipt_entry.as_ref() {
                            let (receipt_index, encoded_receipt) = receipt_entry.entry();
                            // The original atomic commit must already
                            // contain the exact receipt bytes. A replay
                            // never patches a missing/conflicting entry.
                            Self::write_receipt_chain_entry_in(
                                &write_txn,
                                receipt_index,
                                encoded_receipt,
                                false,
                            )?;
                        }
                        if let Some(faithful) = faithful.as_ref() {
                            // The replay checks below include the
                            // attested-root table, whose helper updates
                            // METADATA on fresh writes and therefore
                            // intentionally refuses a concurrently-live
                            // table handle even for exact replay.
                            drop(meta);
                            verify_replayed_faithful_notes_in(
                                &write_txn,
                                faithful.envelope,
                                note_commitments,
                                durable_note_count,
                            )?;
                            verify_replayed_nullifiers_in(&write_txn, faithful)?;
                            crate::faithful_note_root_history::append_faithful_note_root_verified_in(
                                        &write_txn,
                                        faithful.envelope,
                                        faithful.initial_anchor,
                                        true,
                                    )?;
                            crate::federation::store_attested_root_in(
                                &write_txn,
                                faithful.attested_root,
                                crate::federation::AttestedRootWrite::ExactReplay,
                            )?;
                            crate::finalized_faithful_spend::write_finalized_faithful_spends_in(
                                &write_txn,
                                record,
                                faithful.attested_root,
                                faithful.finalized_spends,
                                false,
                            )?;
                        }
                        if let Some(raw_galley) = poa_galley.as_ref() {
                            let faithful = faithful.as_ref().ok_or_else(|| {
                                StoreError::Integrity(
                                    "raw Galley replay omitted its faithful finality weld"
                                        .to_string(),
                                )
                            })?;
                            if executor_state.is_none() {
                                return Err(StoreError::Integrity(
                                    "raw Galley replay omitted its executor-state weld".to_string(),
                                ));
                            }
                            let receipt_entry = receipt_entry.as_ref().ok_or_else(|| {
                                StoreError::Integrity(
                                    "raw Galley replay omitted its exact receipt weld".to_string(),
                                )
                            })?;
                            let (_, encoded_receipt) = receipt_entry.entry();
                            let canonical_raw = postcard::to_stdvec(raw_galley.receipt)
                                .map_err(|error| StoreError::Serialization(error.to_string()))?;
                            if canonical_raw.as_slice() != encoded_receipt {
                                return Err(StoreError::Integrity(
                                    "raw Galley receipt differs from the exact replayed receipt"
                                        .to_string(),
                                ));
                            }
                            let stored_batch = crate::poa_event_batch_v2::load_poa_event_batch_v2_in(
                                            &write_txn,
                                            expected_ordinal,
                                        )?
                                        .ok_or_else(|| {
                                            StoreError::Integrity(
                                                "raw Galley replay invented a batch for a generic finalized turn"
                                                    .to_string(),
                                            )
                                        })?;
                            let activated = crate::poa_activated_content::prepare_historical_poa_galley_policy_v1_in(
                                            &write_txn,
                                            stored_batch.coordinate().world(),
                                        )?;
                            let policy =
                                crate::AuthenticatedPoaGalleyPolicyV1::from_activated_content(
                                    activated,
                                )?;
                            let finality = ValidatedPoaGalleyFinalityWeldV1 {
                                ordinal: existing.ordinal,
                                block_id: existing.block_id,
                                turn_hash: existing.turn_hash,
                                receipt_hash: existing.receipt_hash,
                            };
                            let finalized = crate::poa_galley_authority::derive_poa_finalized_public_perform_v1(
                                            &policy,
                                            &finality,
                                            raw_galley.signed_turn,
                                            raw_galley.receipt,
                                            record,
                                        )?;
                            if finalized.coordinate() != stored_batch.coordinate() {
                                return Err(StoreError::Integrity(
                                            "raw Galley replay finality coordinate differs from stored batch"
                                                .to_string(),
                                        ));
                            }
                            crate::poa_event_batch_v2::verify_replayed_poa_event_batch_in(
                                &write_txn,
                                expected_ordinal,
                                &existing,
                                Some(&stored_batch),
                            )?;
                            crate::poa_holding_consumption::verify_replayed_poa_holding_consumption_in(
                                        &write_txn,
                                        expected_ordinal,
                                        &existing,
                                        None,
                                    )?;
                            let _ = faithful;
                        }
                        let (committed_head, replayed_core_id) = match exact_fnsp_v3.as_ref() {
                            #[cfg(test)]
                            Some(ExactFnspV3Weld::AccumulatorOnly(exact)) => {
                                crate::exact_fnsp_v3_state::verify_replayed_exact_fnsp_v3_append_in(
                                            &write_txn,
                                            *exact,
                                        )?;
                                (None, None)
                            }
                            Some(ExactFnspV3Weld::Frame {
                                exact,
                                activation,
                                frame,
                            }) => {
                                crate::exact_fnsp_v3_state::verify_replayed_exact_fnsp_v3_append_in(
                                            &write_txn,
                                            *exact,
                                        )?;
                                crate::exact_fnsp_v3_frame_head::verify_replayed_exact_fnsp_v3_frame_with_activation_in(
                                            &write_txn,
                                            *exact,
                                            activation.as_ref(),
                                            frame,
                                        )?;
                                let faithful = faithful.as_ref().ok_or_else(|| {
                                    StoreError::Integrity(
                                        "exact frame replay omitted faithful consensus coordinates"
                                            .to_string(),
                                    )
                                })?;
                                let receipt_entry = receipt_entry.as_ref().ok_or_else(|| {
                                    StoreError::Integrity(
                                        "exact frame replay omitted durable receipt coordinates"
                                            .to_string(),
                                    )
                                })?;
                                let (receipt_index, encoded_receipt) = receipt_entry.entry();
                                if receipt_index != frame.receipt_log_index() {
                                    return Err(StoreError::Integrity(
                                        "exact frame replay receipt index disagrees with frame"
                                            .to_string(),
                                    ));
                                }
                                let core_id = crate::finalized_receipt_core_v1::verify_replayed_finalized_receipt_core_in(
                                            &write_txn,
                                            &existing,
                                            receipt_index,
                                            frame.predecessor_receipt_index(),
                                            frame.predecessor_receipt_hash(),
                                            encoded_receipt,
                                            faithful,
                                        )?;
                                (
                                            Some(crate::CommittedExactFnspV3FrameHeadV1::from_verified_durable(
                                                frame.clone(),
                                            )),
                                            Some(core_id),
                                        )
                            }
                            None => (None, None),
                        };
                        // Already durably committed; nothing to do. The
                        // welded notes/burns were written by the original
                        // commit; signal a replay so the caller does NOT
                        // re-apply purely-in-RAM derived state.
                        return Ok(WeldedCommitOutcome {
                            outcome: CommitOutcome {
                                ordinal: expected_ordinal,
                                freshly_committed: false,
                            },
                            committed_head,
                            finalized_receipt_core_id: replayed_core_id,
                        });
                    }
                    return Err(StoreError::Integrity(format!(
                        "commit_finalized_turn: ordinal {expected_ordinal} already holds a \
                         different turn (stored turn_hash != supplied)"
                    )));
                }
                return Err(StoreError::Integrity(format!(
                    "commit_finalized_turn: expected ordinal {expected_ordinal} but durable cursor \
                     is {cursor}; refusing to write a gap (torn-state guard)"
                )));
            }

            // Once the fully audited faithful/exact bridge is installed it is the required shadow
            // authority for every faithful nullifier append, even in the interval between exact
            // bootstrap and first-frame activation. A fresh faithful-only commit would advance the
            // public spend history while leaving the rolling induction boundary and exact
            // accumulator behind. Historical idempotent replay is handled above.
            if faithful
                .as_ref()
                .is_some_and(|faithful| !faithful.spent_nullifiers.is_empty())
                && exact_fnsp_v3.is_none()
                && crate::exact_fnsp_v3_faithful_bridge::installed_in(&write_txn)?
            {
                return Err(StoreError::Integrity(
                    "faithful nullifier growth after exact FNSP-v3 bootstrap requires the exact frame/CAS weld"
                        .to_string(),
                ));
            }

            // Validate the complete durable predecessor and compute the exact
            // successor nullifier root before writing even the commit record.
            // The later inserts use the returned dense append rank inside this
            // same transaction, so an attested root can never float free of the
            // nullifier mutation it claims.
            let fresh_nullifier_seq = faithful
                .as_ref()
                .map(|faithful| verify_fresh_nullifiers_in(&write_txn, faithful))
                .transpose()?;

            assigned = cursor;
            let stored_record = CommitRecord {
                ordinal: assigned,
                ..record.clone()
            };
            let encoded = postcard::to_stdvec(&stored_record)
                .map_err(|e| StoreError::Serialization(e.to_string()))?;

            // 1. Append the commit record.
            {
                let mut log = write_txn.open_table(tables::COMMIT_LOG)?;
                log.insert(assigned, encoded.as_slice())?;
            }

            // 2. Insert the secondary index entries (same txn → never torn).
            {
                let mut idx_receipt = write_txn.open_table(tables::IDX_RECEIPT_BY_HASH)?;
                idx_receipt.insert(&stored_record.receipt_hash, assigned)?;

                let mut idx_turn = write_txn.open_table(tables::IDX_TURN_BY_HASH)?;
                idx_turn.insert(&stored_record.turn_hash, assigned)?;

                let hc_key = CommitRecord::height_creator_key(
                    stored_record.height,
                    &stored_record.creator,
                    assigned,
                );
                let mut idx_hc = write_txn.open_table(tables::IDX_TURN_BY_HEIGHT_CREATOR)?;
                idx_hc.insert(hc_key.as_slice(), assigned)?;

                let mut idx_cell = write_txn.open_table(tables::IDX_CELL_BY_ID)?;
                for cell in &stored_record.touched_cells {
                    let cell_bytes = postcard::to_stdvec(cell)
                        .map_err(|e| StoreError::Serialization(e.to_string()))?;
                    idx_cell.insert(&cell.id().0, cell_bytes.as_slice())?;
                }
                // A removed cell (MakeSovereign) must DROP its cell-by-id entry, or
                // a point `lookup_cell` would resurrect the stale hosted snapshot.
                for id in &stored_record.removed {
                    idx_cell.remove(id)?;
                }
            }

            // The generic per-cell provenance projection is part of the same
            // finalized-turn durability event. Removals advance the head too:
            // a later recreation of the id must extend the removing receipt.
            crate::per_cell_receipt_heads::stage_fresh_per_cell_receipt_heads_in(
                &write_txn,
                &stored_record,
            )?;

            // 3. Burn the turn's forever digests in the SAME transaction (the
            //    same-transaction burn weld): the record and its anti-replay
            //    burns are one atomic durability event.
            if !burns.is_empty() {
                let mut forever = write_txn.open_table(tables::FOREVER_DIGESTS)?;
                for (namespace, scope, digest) in burns {
                    let key = crate::forever_digests::forever_key(*namespace, scope, digest);
                    forever.insert(&key, ())?;
                }
            }

            // Reconstruct the faithful predecessor/successor from the exact
            // durable leaf prefix BEFORE adding the new leaves.  This is the
            // semantic check that keeps the signed edge from floating free of
            // the mutation it authorizes.
            let durable_note_count = meta
                .get(tables::META_NOTE_TREE_SIZE)?
                .map(|guard| guard.value())
                .unwrap_or(0);
            if let Some(faithful) = faithful.as_ref() {
                verify_fresh_faithful_notes_in(
                    &write_txn,
                    faithful.envelope,
                    note_commitments,
                    durable_note_count,
                )?;
            }

            let executor_note_count = executor_state
                .map(|state| {
                    crate::executor_consensus_state::stage_fresh_executor_consensus_state_in(
                        &write_txn,
                        assigned,
                        durable_note_count,
                        note_commitments,
                        state,
                    )
                })
                .transpose()?;

            if let Some(state) = executor_state {
                crate::promise_resolutions::stage_fresh_promise_resolution_batch_in(
                    &write_txn,
                    &stored_record,
                    &state.promise_resolutions,
                )?;
            }

            // 3b. Append note-tree leaves in the SAME transaction (the
            //     same-transaction NOTE weld, bug #58): the record and every
            //     `NoteCreate` commitment it produced are one atomic durability
            //     event, so a crash can never leave a note leaf durable without
            //     its turn (the double-apply that permanently diverged the
            //     note-tree root). Positions are assigned sequentially from the
            //     current durable size, mirroring `store_note_commitment`.
            if let Some(size) = executor_note_count {
                meta.insert(tables::META_NOTE_TREE_SIZE, size)?;
                if size != durable_note_count {
                    let mut meta_bytes = write_txn.open_table(tables::METADATA_BYTES)?;
                    meta_bytes.remove(tables::META_NOTE_TREE_ROOT_CACHE)?;
                }
            } else if !note_commitments.is_empty() {
                let mut size = durable_note_count;
                {
                    let mut notes = write_txn.open_table(tables::NOTE_COMMITMENTS)?;
                    for cm in note_commitments {
                        notes.insert(size, cm)?;
                        size += 1;
                    }
                }
                meta.insert(tables::META_NOTE_TREE_SIZE, size)?;
                // Invalidate the cached note-tree root within the same txn, so
                // the next `note_tree_root()` recomputes over the new leaves.
                let mut meta_bytes = write_txn.open_table(tables::METADATA_BYTES)?;
                meta_bytes.remove(tables::META_NOTE_TREE_ROOT_CACHE)?;
            }

            // 3c. Insert the spent-nullifier presence rows AND the public
            // value/append-sequence records that reconstruct the attested
            // eight-felt accumulator. This shares the carrying turn's atomic
            // boundary; duplicate/replayed nullifiers cannot be warned away.
            if let (Some(faithful), Some(first_seq)) = (faithful.as_ref(), fresh_nullifier_seq) {
                append_fresh_nullifiers_in(&write_txn, faithful.spent_nullifiers, first_seq)?;
                if exact_bridge_append.is_some() {
                    let [spend] = faithful.spent_nullifiers else {
                        return Err(StoreError::Integrity(
                            "exact faithful bridge requires exactly one independently derived faithful append"
                                .to_string(),
                        ));
                    };
                    faithful_bridge_append =
                        Some(dregg_circuit::exact_nullifier_aafi::ExactAppendRecord {
                            seq: first_seq,
                            raw: spend.nullifier,
                            value: spend.value,
                        });
                }
            }

            // `store_attested_root_in` also updates the latest-root coordinate
            // in METADATA. redb deliberately refuses a second open of the same
            // table while this handle is live, so release it before entering
            // the attestation/history portion of the same transaction. The
            // commit cursor is reopened and advanced last below.
            drop(meta);

            // 3d. The exact faithful root edge and its signed live attestation
            // share the note leaves' atomic boundary.  Verify both roots from
            // the durable pre-image before mutating the history table.
            if let Some(faithful) = faithful.as_ref() {
                crate::faithful_note_root_history::append_faithful_note_root_verified_in(
                    &write_txn,
                    faithful.envelope,
                    faithful.initial_anchor,
                    false,
                )?;
                crate::federation::store_attested_root_in(
                    &write_txn,
                    faithful.attested_root,
                    crate::federation::AttestedRootWrite::Fresh,
                )?;
                crate::finalized_faithful_spend::write_finalized_faithful_spends_in(
                    &write_txn,
                    &stored_record,
                    faithful.attested_root,
                    faithful.finalized_spends,
                    true,
                )?;
            }

            // 3e. Weld the immutable receipt-log entry into this same atomic
            // transaction. This is deliberately before the cursor advance;
            // redb commits all writes together or none of them.
            if let Some(receipt_entry) = receipt_entry.as_ref() {
                let (receipt_index, encoded_receipt) = receipt_entry.entry();
                Self::write_receipt_chain_entry_in(
                    &write_txn,
                    receipt_index,
                    encoded_receipt,
                    receipt_entry.allow_insert(),
                )?;
            }

            // 3f. Project the exact receipt into its signer-independent semantic core only after
            // the canonical receipt row is staged. The store derives the core from authenticated
            // consensus coordinates and the durable per-agent predecessor; callers never supply
            // a pre-hashed identity that could be detached from this transaction.
            if let Some(ExactFnspV3Weld::Frame { frame, .. }) = exact_fnsp_v3.as_ref() {
                let faithful = faithful.as_ref().ok_or_else(|| {
                    StoreError::Integrity(
                        "exact frame omitted faithful consensus coordinates".to_string(),
                    )
                })?;
                let receipt_entry = receipt_entry.as_ref().ok_or_else(|| {
                    StoreError::Integrity(
                        "exact frame omitted durable receipt coordinates".to_string(),
                    )
                })?;
                let (receipt_index, encoded_receipt) = receipt_entry.entry();
                if receipt_index != frame.receipt_log_index() {
                    return Err(StoreError::Integrity(
                        "exact frame receipt index disagrees with receipt weld".to_string(),
                    ));
                }
                finalized_receipt_core_id = Some(
                    crate::finalized_receipt_core_v1::stage_fresh_finalized_receipt_core_in(
                        &write_txn,
                        &stored_record,
                        receipt_index,
                        frame.predecessor_receipt_index(),
                        frame.predecessor_receipt_hash(),
                        encoded_receipt,
                        faithful,
                    )?,
                );
            }

            if let Some(raw_galley) = poa_galley.as_ref() {
                if faithful.is_none() || executor_state.is_none() {
                    return Err(StoreError::Integrity(
                        "raw Galley commit requires faithful and executor-state welds".to_string(),
                    ));
                }
                let receipt_entry = receipt_entry.as_ref().ok_or_else(|| {
                    StoreError::Integrity(
                        "raw Galley commit omitted its exact receipt weld".to_string(),
                    )
                })?;
                let (_, encoded_receipt) = receipt_entry.entry();
                let canonical_raw = postcard::to_stdvec(raw_galley.receipt)
                    .map_err(|error| StoreError::Serialization(error.to_string()))?;
                if canonical_raw.as_slice() != encoded_receipt {
                    return Err(StoreError::Integrity(
                        "raw Galley receipt differs from the staged exact receipt".to_string(),
                    ));
                }
                let activated =
                    crate::poa_activated_content::prepare_active_poa_galley_policy_v1_in(
                        &write_txn,
                    )?;
                let policy =
                    crate::AuthenticatedPoaGalleyPolicyV1::from_activated_content(activated)?;
                let finality = ValidatedPoaGalleyFinalityWeldV1 {
                    ordinal: stored_record.ordinal,
                    block_id: stored_record.block_id,
                    turn_hash: stored_record.turn_hash,
                    receipt_hash: stored_record.receipt_hash,
                };
                let finalized =
                    crate::poa_galley_authority::derive_poa_finalized_public_perform_v1(
                        &policy,
                        &finality,
                        raw_galley.signed_turn,
                        raw_galley.receipt,
                        &stored_record,
                    )?;
                let sealed = self
                    .prepare_poa_galley_public_event_batch_v1_in(&write_txn, &policy, finalized)?;
                let batch = sealed.into_event_batch();
                validate_poa_v2_batch_authority(&stored_record, encoded_receipt, &batch, None)?;
                crate::poa_event_batch_v2::stage_fresh_poa_event_batch_in(
                    &write_txn,
                    assigned,
                    &stored_record,
                    &batch,
                )?;
            }

            if let Some(poa_signal) = poa_signal {
                crate::poa_signal_state::stage_fresh_poa_signal_transition_in(
                    &write_txn,
                    assigned,
                    &stored_record,
                    poa_signal,
                )?;
            }
            if let Some(poa_event) = poa_event {
                crate::poa_event_store::stage_fresh_poa_event_in(
                    &write_txn,
                    assigned,
                    &stored_record,
                    poa_event,
                )?;
            }
            if let Some(poa_batch) = poa_batch {
                crate::poa_world_activation::require_poa_active_world_exact_in(
                    &write_txn,
                    poa_batch.coordinate().world(),
                )?;
                crate::poa_event_batch_v2::stage_fresh_poa_event_batch_in(
                    &write_txn,
                    assigned,
                    &stored_record,
                    poa_batch,
                )?;
            }
            if let Some(poa_holding) = poa_holding {
                crate::poa_holding_consumption::stage_fresh_poa_holding_consumption_in(
                    &write_txn,
                    assigned,
                    &stored_record,
                    poa_holding,
                )?;
            }

            // 4. Advance the durable cursor LAST within the txn (still atomic).
            let mut meta = write_txn.open_table(tables::METADATA)?;
            meta.insert(tables::META_COMMIT_CURSOR, assigned + 1)?;
        }
        // The exact append is deliberately the final staged mutation.  This helper CONSUMES the
        // writer and returns it only after independently replaying the durable prefix and writing
        // both the append record and successor head.  Any stale/forged/late storage failure drops
        // the sole transaction here, so none of the finalized-turn rows above can leak through.
        let (write_txn, staged_frame) = match exact_fnsp_v3 {
            #[cfg(test)]
            Some(ExactFnspV3Weld::AccumulatorOnly(exact)) => {
                let (write, _) =
                    crate::exact_fnsp_v3_state::compare_and_commit_exact_fnsp_v3_append_in(
                        write_txn, exact,
                    )?;
                (write, None)
            }
            Some(ExactFnspV3Weld::Frame {
                exact,
                activation,
                frame,
            }) => {
                let (write, staged) =
                    crate::exact_fnsp_v3_frame_head::stage_exact_fnsp_v3_frame_with_activation_in(
                        write_txn, exact, activation, frame,
                    )?;
                (write, Some(staged))
            }
            None => (write_txn, None),
        };
        match (faithful_bridge_append, exact_bridge_append) {
            (Some(faithful), Some(exact)) => {
                crate::exact_fnsp_v3_faithful_bridge::stage_matching_append_in(
                    &write_txn, faithful, exact,
                )?;
            }
            (None, None) => {}
            _ => {
                return Err(StoreError::Integrity(
                    "exact finalized turn did not stage both faithful/exact bridge projections"
                        .to_string(),
                ));
            }
        }
        // The caller's config blobs, in THIS transaction (the same
        // together-or-not-at-all boundary as the commit record, and the same
        // single fsync). Opened in its own scope so no later helper can find the
        // table handle still live. Empty for every caller that has nothing to
        // weld — byte-identical to not passing it.
        if !config_blobs.is_empty() {
            let mut cfg = write_txn.open_table(tables::METADATA_BYTES)?;
            for (key, value) in config_blobs {
                cfg.insert(*key, *value)?;
            }
        }
        write_txn.commit()?;
        Ok(WeldedCommitOutcome {
            outcome: CommitOutcome {
                ordinal: assigned,
                freshly_committed: true,
            },
            committed_head: staged_frame
                .map(crate::CommittedExactFnspV3FrameHeadV1::from_verified_durable),
            finalized_receipt_core_id,
        })
    }

    // =========================================================================
    // Commit-log reads
    // =========================================================================

    /// Load the commit record at an ordinal.
    pub fn commit_record_at(&self, ordinal: u64) -> Result<Option<CommitRecord>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::COMMIT_LOG)?;
        match table.get(ordinal)? {
            Some(guard) => Ok(Some(decode_commit_record(guard.value())?)),
            None => Ok(None),
        }
    }

    /// Load the immutable finalized authority coordinates for a live or compacted commit.
    ///
    /// Unlike [`Self::commit_record_at`], this remains available below the compaction floor. A
    /// compacted result comes only from the audited dense certificate chain; it is sufficient for
    /// PoA semantic replay but cannot be used to re-apply the checkpoint-subsumed write set.
    pub fn finalized_commit_authority_at(
        &self,
        ordinal: u64,
    ) -> Result<Option<crate::FinalizedCommitAuthorityV1>> {
        let read_txn = self.db.begin_read()?;
        let compacted_floor = read_txn
            .open_table(tables::METADATA)?
            .get(tables::META_COMMIT_COMPACTED)?
            .map(|value| value.value())
            .unwrap_or(0);
        if ordinal < compacted_floor {
            let certificates = crate::poa_compact_authority::load_audited_certificates_in_read(
                &read_txn,
                compacted_floor,
            )?;
            return Ok(certificates
                .get(&ordinal)
                .map(|certificate| certificate.authority()));
        }
        let table = read_txn.open_table(tables::COMMIT_LOG)?;
        table
            .get(ordinal)?
            .map(|guard| {
                decode_commit_record(guard.value())
                    .and_then(|record| crate::FinalizedCommitAuthorityV1::from_record(&record))
            })
            .transpose()
    }

    /// The blocklace `block_id` of every durably committed turn this node has
    /// applied — the LIVE-log ids followed by any COMPACTED ids.
    ///
    /// This is the exact identity set of turn-carrying blocks this node has
    /// durably applied (each id was written atomically with its turn's ledger
    /// commit), and is the turn half of the node's identity execution cursor on
    /// recovery: a turn block is re-executed after a restart iff its id is NOT
    /// here — no lost finalized turn, no double-apply.
    ///
    /// COMPACTION-STABILITY (load-bearing for no-double-apply): the contract is
    /// "every APPLIED turn's id appears here", NOT "every id in the live log".
    /// [`Self::compact_below`] removes a subsumed record from the live log but
    /// records its id in `COMMIT_COMPACTED_BLOCK_IDS`; this method unions that
    /// set back in, so the returned identity set is INVARIANT under compaction —
    /// a compacted (already-applied) turn is still reported as applied and is
    /// never re-executed on top of the checkpoint that already includes it.
    pub fn commit_log_block_ids(&self) -> Result<Vec<[u8; 32]>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::COMMIT_LOG)?;
        let mut out = Vec::new();
        // Live records first, in ordinal order.
        for entry in table.range(0u64..)? {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            let record = decode_commit_record(entry.1.value())?;
            out.push(record.block_id);
        }
        // Then the ids of turns whose records were compacted away — still
        // applied, must remain in the identity execution cursor.
        let compacted = read_txn.open_table(tables::COMMIT_COMPACTED_BLOCK_IDS)?;
        for entry in compacted.iter()? {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            out.push(*entry.0.value());
        }
        Ok(out)
    }

    /// Load every commit record from `start` (inclusive) to the cursor, in order.
    ///
    /// This is the replay source for recovery: feeding these records' post-state
    /// cell snapshots back over the last ledger checkpoint reconstructs the exact
    /// finalized ledger up to the cursor.
    pub fn commit_records_from(&self, start: u64) -> Result<Vec<CommitRecord>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::COMMIT_LOG)?;
        let mut out = Vec::new();
        for entry in table.range(start..)? {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            out.push(decode_commit_record(entry.1.value())?);
        }
        Ok(out)
    }

    /// The block-level high-water mark to resume blocklace processing from on
    /// recovery: the `block_executed_up_to` of the last durably-committed turn,
    /// or 0 if no turn has been committed.
    ///
    /// This is the crash-consistent replacement for the separately-written
    /// `BLOCKLACE_EXECUTED_UP_TO_KEY`: it was written inside the same transaction
    /// as the turn it accompanies, so it can never be ahead of the durable
    /// ledger/commit-log.
    pub fn recovered_block_cursor(&self) -> Result<u64> {
        let cursor = self.commit_cursor()?;
        if cursor == 0 {
            return Ok(0);
        }
        match self.commit_record_at(cursor - 1)? {
            Some(rec) => Ok(rec.block_executed_up_to),
            None => Err(StoreError::Integrity(format!(
                "recovered_block_cursor: cursor {cursor} but no record at {}",
                cursor - 1
            ))),
        }
    }

    /// The durable post-state ledger root the node converged to: the
    /// `ledger_root` of the last committed turn, or `None` if no turn committed.
    ///
    /// A recovered node that reconstructs its ledger MUST reproduce this root
    /// (it is the on-chain-style commitment of the finalized state). This is the
    /// recovery-side analogue of LaceMerge convergence: independent of HOW the
    /// ledger is rebuilt (replay vs checkpoint+overlay), the resulting root must
    /// equal the root the committing node recorded.
    pub fn recovered_ledger_root(&self) -> Result<Option<[u8; 32]>> {
        let cursor = self.commit_cursor()?;
        if cursor == 0 {
            return Ok(None);
        }
        Ok(self.commit_record_at(cursor - 1)?.map(|r| r.ledger_root))
    }

    /// The finalized HEIGHT the node converged to: the `height` of the last
    /// committed turn, or `None` if no turn committed. Used by the boot-time
    /// anti-rollback check (NODE-2): a recovered store whose head height is BELOW a
    /// previously-witnessed signed finalization / high-water mark is a rollback and
    /// must be refused.
    pub fn recovered_head_height(&self) -> Result<Option<u64>> {
        let cursor = self.commit_cursor()?;
        if cursor == 0 {
            return Ok(None);
        }
        Ok(self.commit_record_at(cursor - 1)?.map(|r| r.height))
    }

    /// The last-writer-wins overlay of cell post-states committed since the most
    /// recent full ledger checkpoint at `checkpoint_height`.
    ///
    /// Returns the post-state of every cell touched by a committed turn whose
    /// `height > checkpoint_height`. Overlaying these on the checkpoint ledger
    /// reconstructs the finalized ledger up to the commit cursor WITHOUT
    /// re-executing — the cell-by-id index is exactly this overlay maintained
    /// incrementally, but this method re-derives it from the log so recovery
    /// never trusts the (rebuildable) index for correctness.
    pub fn cell_overlay_since(&self, checkpoint_height: u64) -> Result<Vec<CellOverlayOp>> {
        use std::collections::HashMap;
        let read_txn = self.db.begin_read()?;
        let log = read_txn.open_table(tables::COMMIT_LOG)?;
        // ordinal-ascending iteration → later writers/removals overwrite earlier
        // ops for the same id (last-writer-wins over the resolved op). A cell
        // upserted then later removed ends REMOVED; removed then re-created ends
        // upserted — the resolution mirrors the Lean `Write = insert | remove`
        // fold whose observable is the final map.
        let mut latest: HashMap<[u8; 32], CellOverlayOp> = HashMap::new();
        for entry in log.iter()? {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            let record = decode_commit_record(entry.1.value())?;
            if record.height <= checkpoint_height {
                continue;
            }
            // Within a record: upserts first, then removals (a removal wins if a
            // cell were somehow both — MakeSovereign only removes, never touches).
            for cell in record.touched_cells {
                latest.insert(cell.id().0, CellOverlayOp::Upsert(cell));
            }
            for id in record.removed {
                latest.insert(id, CellOverlayOp::Remove(CellId(id)));
            }
        }
        Ok(latest.into_values().collect())
    }

    /// The cell ids REMOVED (net) from the hosted set since the checkpoint —
    /// the tombstones of [`cell_overlay_since`] resolved last-writer-wins (a cell
    /// removed then re-created is NOT reported). The node's genesis-baseline
    /// reconstruction (`reseed_genesis_then_overlay`) re-materializes ALL genesis
    /// cells on a fresh ledger, so a genesis cell removed post-checkpoint (e.g.
    /// made sovereign) must be deleted AGAIN after the baseline is laid down, or
    /// the fresh genesis copy resurrects it (and the convergence check fails).
    pub fn removed_cell_ids_since(&self, checkpoint_height: u64) -> Result<Vec<CellId>> {
        Ok(self
            .cell_overlay_since(checkpoint_height)?
            .into_iter()
            .filter_map(|op| match op {
                CellOverlayOp::Remove(id) => Some(id),
                CellOverlayOp::Upsert(_) => None,
            })
            .collect())
    }

    // =========================================================================
    // Secondary index lookups
    // =========================================================================

    /// Resolve a receipt hash to its commit record (receipt-by-hash index).
    pub fn lookup_receipt(&self, receipt_hash: &[u8; 32]) -> Result<Option<CommitRecord>> {
        self.lookup_by_index(tables::IDX_RECEIPT_BY_HASH, receipt_hash)
    }

    /// Resolve a turn hash to its commit record (turn-by-hash index).
    pub fn lookup_turn(&self, turn_hash: &[u8; 32]) -> Result<Option<CommitRecord>> {
        self.lookup_by_index(tables::IDX_TURN_BY_HASH, turn_hash)
    }

    fn lookup_by_index(
        &self,
        idx: redb::TableDefinition<&[u8; 32], u64>,
        key: &[u8; 32],
    ) -> Result<Option<CommitRecord>> {
        let read_txn = self.db.begin_read()?;
        let index = read_txn.open_table(idx)?;
        let ordinal = match index.get(key)? {
            Some(g) => g.value(),
            None => return Ok(None),
        };
        let log = read_txn.open_table(tables::COMMIT_LOG)?;
        match log.get(ordinal)? {
            Some(guard) => Ok(Some(decode_commit_record(guard.value())?)),
            None => Err(StoreError::Integrity(format!(
                "index points at ordinal {ordinal} but commit log has no record there"
            ))),
        }
    }

    /// Look up the current durable snapshot of a cell by id (cell-by-id index).
    ///
    /// Returns the latest post-state of the cell among all committed turns that
    /// touched it. `None` means no committed turn has touched this cell since the
    /// last full ledger checkpoint (callers fall back to the checkpoint).
    pub fn lookup_cell(&self, cell_id: &CellId) -> Result<Option<Cell>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::IDX_CELL_BY_ID)?;
        match table.get(&cell_id.0)? {
            Some(guard) => Ok(Some(postcard::from_bytes(guard.value())?)),
            None => Ok(None),
        }
    }

    /// All commit records at a given height, in creator order (turns-by-height).
    pub fn turns_at_height(&self, height: u64) -> Result<Vec<CommitRecord>> {
        let lo = CommitRecord::height_creator_key(height, &[0u8; 32], 0);
        let hi = CommitRecord::height_creator_key(height, &[0xffu8; 32], u64::MAX);
        self.turns_in_key_range(lo.as_slice(), hi.as_slice(), true)
    }

    /// All commit records by a given creator, in height order (turns-by-creator).
    ///
    /// Scans the `(height, creator)` index and filters by creator. Height-major
    /// key layout means the results come back height-ordered.
    pub fn turns_by_creator(&self, creator: &[u8; 32]) -> Result<Vec<CommitRecord>> {
        let read_txn = self.db.begin_read()?;
        let index = read_txn.open_table(tables::IDX_TURN_BY_HEIGHT_CREATOR)?;
        let log = read_txn.open_table(tables::COMMIT_LOG)?;
        let mut out = Vec::new();
        for entry in index.iter()? {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            let key = entry.0.value();
            if key.len() == 48 && &key[8..40] == creator.as_slice() {
                let ordinal = entry.1.value();
                if let Some(guard) = log.get(ordinal)? {
                    out.push(decode_commit_record(guard.value())?);
                }
            }
        }
        Ok(out)
    }

    fn turns_in_key_range(
        &self,
        lo: &[u8],
        hi: &[u8],
        inclusive_hi: bool,
    ) -> Result<Vec<CommitRecord>> {
        let read_txn = self.db.begin_read()?;
        let index = read_txn.open_table(tables::IDX_TURN_BY_HEIGHT_CREATOR)?;
        let log = read_txn.open_table(tables::COMMIT_LOG)?;
        let mut out = Vec::new();
        let iter = if inclusive_hi {
            index.range(lo..=hi)?
        } else {
            index.range(lo..hi)?
        };
        for entry in iter {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            let ordinal = entry.1.value();
            if let Some(guard) = log.get(ordinal)? {
                out.push(decode_commit_record(guard.value())?);
            }
        }
        Ok(out)
    }

    // =========================================================================
    // Index ⟺ log invariant: verify + rebuild
    // =========================================================================

    /// Verify the "index entry exists iff the log has it" invariant.
    ///
    /// Walks the commit log and checks that each record's three hash-index
    /// entries resolve back to that record's ordinal, then walks each index and
    /// checks that no entry is an orphan (points at a missing record) or points
    /// at a record that does not carry that key. The cell-by-id index is checked
    /// for being a subset of the log's touched cells (it is a last-writer-wins
    /// projection, so its agreement criterion is "every cell entry equals the
    /// latest log record that touched that cell").
    pub fn verify_index_agrees_with_log(&self) -> Result<IndexAuditReport> {
        let mut report = IndexAuditReport {
            cursor: self.commit_cursor()?,
            compacted: self.commit_compacted_floor()?,
            ..Default::default()
        };

        let read_txn = self.db.begin_read()?;
        let log = read_txn.open_table(tables::COMMIT_LOG)?;
        let idx_receipt = read_txn.open_table(tables::IDX_RECEIPT_BY_HASH)?;
        let idx_turn = read_txn.open_table(tables::IDX_TURN_BY_HASH)?;
        let idx_hc = read_txn.open_table(tables::IDX_TURN_BY_HEIGHT_CREATOR)?;
        let idx_cell = read_txn.open_table(tables::IDX_CELL_BY_ID)?;

        // Forward direction: every log record has its index entries.
        // Also track the latest ordinal that touched each cell so we can check
        // the cell index is the correct last-writer-wins projection.
        use std::collections::HashMap;
        let mut latest_cell_writer: HashMap<[u8; 32], (u64, Cell)> = HashMap::new();

        for entry in log.iter()? {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            let ordinal = entry.0.value();
            let record = decode_commit_record(entry.1.value())?;
            report.records += 1;

            check_hash_index(
                &idx_receipt,
                &record.receipt_hash,
                ordinal,
                "receipt_by_hash",
                &mut report,
            )?;
            check_hash_index(
                &idx_turn,
                &record.turn_hash,
                ordinal,
                "turn_by_hash",
                &mut report,
            )?;
            let hc_key = CommitRecord::height_creator_key(record.height, &record.creator, ordinal);
            match idx_hc.get(hc_key.as_slice())? {
                Some(g) if g.value() == ordinal => {}
                Some(g) => report.mismatched_entries.push(format!(
                    "turn_by_height_creator(h={}) -> {} but record at ordinal {ordinal}",
                    record.height,
                    g.value()
                )),
                None => report.missing_entries.push(format!(
                    "turn_by_height_creator(h={}) missing for ordinal {ordinal}",
                    record.height
                )),
            }

            for cell in &record.touched_cells {
                latest_cell_writer
                    .entry(cell.id().0)
                    .and_modify(|slot| {
                        if ordinal >= slot.0 {
                            *slot = (ordinal, cell.clone());
                        }
                    })
                    .or_insert((ordinal, cell.clone()));
            }
            for removed in &record.removed {
                latest_cell_writer.remove(removed);
            }
        }

        // Reverse direction: no orphan hash-index entries.
        check_no_orphans(&idx_receipt, &log, "receipt_by_hash", &mut report)?;
        check_no_orphans(&idx_turn, &log, "turn_by_hash", &mut report)?;
        for entry in idx_hc.iter()? {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            let key = entry.0.value();
            let ordinal = entry.1.value();
            if key.len() != 48 {
                // Pre-(height,creator,ordinal) legacy key shape — the boot
                // migration (`migrate_height_creator_index`) rebuilds these.
                report.orphan_entries.push(format!(
                    "turn_by_height_creator legacy {}-byte key -> ordinal {ordinal}",
                    key.len()
                ));
                continue;
            }
            if log.get(ordinal)?.is_none() {
                report.orphan_entries.push(format!(
                    "turn_by_height_creator -> missing ordinal {ordinal}"
                ));
            }
        }

        // Cell index: must equal the last-writer-wins projection of the log.
        let mut cell_index_count = 0u64;
        for entry in idx_cell.iter()? {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            cell_index_count += 1;
            let cell_id = *entry.0.value();
            let stored: Cell = postcard::from_bytes(entry.1.value())?;
            match latest_cell_writer.get(&cell_id) {
                Some((_, expected)) if *expected == stored => {}
                Some(_) => report.mismatched_entries.push(format!(
                    "cell_by_id({}) != latest log writer",
                    hex32(&cell_id)
                )),
                None => report
                    .orphan_entries
                    .push(format!("cell_by_id({}) has no log writer", hex32(&cell_id))),
            }
        }
        if (cell_index_count as usize) < latest_cell_writer.len() {
            for cell_id in latest_cell_writer.keys() {
                if idx_cell.get(cell_id)?.is_none() {
                    report
                        .missing_entries
                        .push(format!("cell_by_id({}) missing", hex32(cell_id)));
                }
            }
        }

        // Unlike the checkpoint-relative cell snapshot index above, generic
        // receipt provenance spans the complete applied history. Its compacted
        // baseline plus live suffix must reproduce the durable current map
        // exactly; structural/cursor/codec disagreement is an integrity error.
        crate::per_cell_receipt_heads::verify_per_cell_receipt_head_index_in(&read_txn)?;

        Ok(report)
    }

    /// Rebuild the entire secondary index from the commit log alone.
    ///
    /// Clears every index table, then replays the log in ordinal order
    /// re-inserting all index entries. After this, the cell-by-id index is the
    /// last-writer-wins projection of the log's `touched_cells`. The commit
    /// cursor is left untouched (the log IS the source of truth). The whole
    /// rebuild runs in a single transaction, so a crash mid-rebuild leaves the
    /// previous (already-consistent) index in place.
    ///
    /// Returns the number of records replayed.
    pub fn rebuild_index_from_log(&self) -> Result<u64> {
        // Rewrites the commit log / per-cell head tables beyond an append.
        let _rewrite = self.per_cell_head_cache.begin_rewrite();
        let write_txn = self.db.begin_write()?;
        let mut replayed = 0u64;
        {
            let (compacted_floor, cursor) = {
                let meta = write_txn.open_table(tables::METADATA)?;
                (
                    meta.get(tables::META_COMMIT_COMPACTED)?
                        .map(|guard| guard.value())
                        .unwrap_or(0),
                    meta.get(tables::META_COMMIT_CURSOR)?
                        .map(|guard| guard.value())
                        .unwrap_or(0),
                )
            };
            // Collect the log first (immutable view), then rewrite indexes.
            let records: Vec<CommitRecord> = {
                let log = write_txn.open_table(tables::COMMIT_LOG)?;
                let mut v = Vec::new();
                for entry in log.iter()? {
                    let entry = entry
                        .map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
                    v.push(decode_commit_record(entry.1.value())?);
                }
                v
            };

            clear_table_u32(&write_txn, tables::IDX_RECEIPT_BY_HASH)?;
            clear_table_u32(&write_txn, tables::IDX_TURN_BY_HASH)?;
            {
                let mut idx_hc = write_txn.open_table(tables::IDX_TURN_BY_HEIGHT_CREATOR)?;
                let keys: Vec<Vec<u8>> = idx_hc
                    .iter()?
                    .filter_map(|e| e.ok().map(|e| e.0.value().to_vec()))
                    .collect();
                for k in keys {
                    idx_hc.remove(k.as_slice())?;
                }
            }
            {
                let mut idx_cell = write_txn.open_table(tables::IDX_CELL_BY_ID)?;
                let keys: Vec<[u8; 32]> = idx_cell
                    .iter()?
                    .filter_map(|e| e.ok().map(|e| *e.0.value()))
                    .collect();
                for k in keys {
                    idx_cell.remove(&k)?;
                }
            }

            let mut idx_receipt = write_txn.open_table(tables::IDX_RECEIPT_BY_HASH)?;
            let mut idx_turn = write_txn.open_table(tables::IDX_TURN_BY_HASH)?;
            let mut idx_hc = write_txn.open_table(tables::IDX_TURN_BY_HEIGHT_CREATOR)?;
            let mut idx_cell = write_txn.open_table(tables::IDX_CELL_BY_ID)?;

            for record in &records {
                idx_receipt.insert(&record.receipt_hash, record.ordinal)?;
                idx_turn.insert(&record.turn_hash, record.ordinal)?;
                let hc_key = CommitRecord::height_creator_key(
                    record.height,
                    &record.creator,
                    record.ordinal,
                );
                idx_hc.insert(hc_key.as_slice(), record.ordinal)?;
                for cell in &record.touched_cells {
                    let cell_bytes = postcard::to_stdvec(cell)
                        .map_err(|e| StoreError::Serialization(e.to_string()))?;
                    idx_cell.insert(&cell.id().0, cell_bytes.as_slice())?;
                }
                for removed in &record.removed {
                    idx_cell.remove(removed)?;
                }
                replayed += 1;
            }

            crate::per_cell_receipt_heads::rebuild_current_per_cell_receipt_heads_in(
                &write_txn,
                compacted_floor,
                cursor,
                &records,
            )?;
        }
        write_txn.commit()?;
        Ok(replayed)
    }

    // =========================================================================
    // Commit-log compaction (bound the WAL below a finalized checkpoint)
    // =========================================================================

    /// Unsigned compatibility entry point. It never deletes: a checkpoint proves subsumption but
    /// does not authenticate the compact carrier which replaces the removed records. Call
    /// [`Self::compact_below_with_poa_anchor_v1`] with a signed exact preview to compact.
    ///
    /// # The safety constraint (provably safe — never best-effort)
    ///
    /// A node reconstructs its finalized ledger as `checkpoint ⊕ overlay`, where
    /// the overlay ([`Self::cell_overlay_since`]) is the post-state of every cell
    /// touched by a record with `record.height > checkpoint_height` — records
    /// with `record.height <= checkpoint_height` contribute NOTHING to the
    /// reconstruction (the checkpoint already folded them in). This is the
    /// machine-checked recovery model `CrashRecovery.recover_eq_replay`: the
    /// checkpoint is `replay genesis (take k)` and the overlay is the writes of
    /// `(drop k)`, so the `take k` records are redundant once the checkpoint
    /// exists.
    ///
    /// Compaction is therefore safe ONLY under a COVERING ledger checkpoint:
    /// the authenticated method removes records iff
    /// `latest_ledger_checkpoint_height() >= height`, and even then only the
    /// contiguous ordinal PREFIX of records with `record.height < height` (it
    /// stops at the first record with `record.height >= height`, so the live log
    /// `[compacted_floor, cursor)` stays dense — no gap is ever punched). Every
    /// removed record has `height < height <= checkpoint_height`, i.e. strictly
    /// below the checkpoint, so the overlay never references it and the
    /// checkpoint subsumes it.
    ///
    /// When there is NO covering checkpoint (`latest_ledger_checkpoint_height()
    /// < height`), this is a **no-op returning 0**: it refuses to delete any
    /// record a checkpoint does not subsume (deleting one would lose a finalized
    /// turn — the load-bearing "no lost finalized turn" invariant). `height == 0`
    /// is likewise a no-op (nothing is below it).
    ///
    /// # What compaction preserves
    ///
    /// * **The durable cursor is UNCHANGED.** [`Self::commit_cursor`] still
    ///   counts every applied turn; only the physical record count drops. The
    ///   compaction floor ([`Self::commit_compacted_floor`]) advances by exactly
    ///   the number removed, so `cursor == len + floor` holds and the
    ///   index-audit density invariant ([`IndexAuditReport::ok`]) is preserved.
    /// * **No lost finalized turn.** Reconstruction is identical before and
    ///   after: `checkpoint ⊕ cell_overlay_since(checkpoint_height)` is unchanged
    ///   because no compacted record was in that overlay (`recover_eq_replay`).
    /// * **No double-apply.** Each compacted turn's `block_id` is recorded in
    ///   `COMMIT_COMPACTED_BLOCK_IDS` in the SAME transaction, so
    ///   [`Self::commit_log_block_ids`] still reports it as applied and the
    ///   identity execution cursor never re-runs it over the checkpoint.
    /// * **The index agrees with the log.** The compacted records' receipt /
    ///   turn / (height, creator) entries are removed, and the cell-by-id index
    ///   is re-derived from the SURVIVING records (last-writer-wins), so
    ///   [`Self::verify_index_agrees_with_log`] stays `ok()`.
    ///
    /// All of the above land in ONE redb transaction (one fsync boundary): a
    /// crash mid-compaction leaves the pre-compaction (already-consistent) state
    /// in place.
    pub fn compact_below(&self, height: u64) -> Result<u64> {
        if height == 0 {
            return Ok(0);
        }
        tracing::debug!(
            requested_height = height,
            "compact_below: deletion requires an externally pinned signed PoA compact checkpoint anchor; refusing before mutation"
        );
        Ok(0)
    }

    /// Delete a checkpoint-subsumed prefix only after a hybrid quorum signed its exact preview.
    ///
    /// `trust_policy` is deployment/genesis-authenticated configuration supplied independently of
    /// this database. The anchor's self-carried roster must equal its exact epoch root, and every
    /// already-stored anchor is reauthenticated under the same policy before the lineage extends.
    pub fn compact_below_with_poa_anchor_v1(
        &self,
        height: u64,
        anchor: crate::SignedPoaCompactCheckpointAnchorV1,
        trust_policy: &crate::PoaCompactTrustPolicyV1,
    ) -> Result<u64> {
        let current_floor = self.commit_compacted_floor()?;
        if anchor.statement().new_floor() <= current_floor {
            if self.has_exact_poa_compact_checkpoint_anchor_v1(&anchor, trust_policy)? {
                // The exact signed transaction already committed and its whole authority lineage
                // re-audited.  This is a successful response-loss retry, not a second deletion.
                return Ok(0);
            }
            return Err(StoreError::Integrity(
                "PoA compact retry names an already-crossed floor but is not the exact stored anchor"
                    .to_owned(),
            ));
        }
        let trust_root = trust_policy.active_root_for_new_statement(anchor.statement())?;
        let anchor = crate::poa_compact_authority::StoredPoaCompactCheckpointAnchorV1::new(
            anchor, trust_root,
        )?;
        self.audit_poa_compact_authority_v1(Some(trust_policy))?;
        self.compact_below_with_verified_poa_anchor_v1(height, anchor)
    }

    fn compact_below_with_verified_poa_anchor_v1(
        &self,
        height: u64,
        anchor: crate::poa_compact_authority::StoredPoaCompactCheckpointAnchorV1,
    ) -> Result<u64> {
        // Rewrites the commit log / per-cell head tables beyond an append.
        let _rewrite = self.per_cell_head_cache.begin_rewrite();
        // ── Refuse without a covering checkpoint (the safety guard) ─────────
        // Compaction is sound only when a finalized ledger checkpoint at/above
        // `height` captures the state the to-be-removed records reconstruct.
        // No such checkpoint ⇒ delete nothing (a no-op refusal), never lose a
        // finalized turn.
        if height == 0 {
            return Ok(0);
        }
        let checkpoint_height = self.latest_ledger_checkpoint_height()?;
        if checkpoint_height < height {
            tracing::debug!(
                requested_height = height,
                checkpoint_height,
                "compact_below: no covering ledger checkpoint at/above the \
                 requested height — refusing (no-op), records are not subsumed"
            );
            return Ok(0);
        }

        let write_txn = self.db.begin_write()?;
        let compacted;
        {
            let old_floor = {
                let meta = write_txn.open_table(tables::METADATA)?;
                meta.get(tables::META_COMMIT_COMPACTED)?
                    .map(|guard| guard.value())
                    .unwrap_or(0)
            };
            // 1. Identify the contiguous ordinal prefix of records strictly
            //    below `height`, collecting what we need to clean up their
            //    index entries, and the SURVIVORS' cells for the cell-index
            //    re-derivation. We stop at the first record with
            //    `height >= height` so the live log never gains a gap.
            struct Doomed {
                ordinal: u64,
                receipt_hash: [u8; 32],
                turn_hash: [u8; 32],
                hc_key: [u8; 48],
                block_id: [u8; 32],
            }
            let mut doomed: Vec<Doomed> = Vec::new();
            let mut doomed_records: Vec<CommitRecord> = Vec::new();
            let mut survivors: Vec<CommitRecord> = Vec::new();
            {
                let log = write_txn.open_table(tables::COMMIT_LOG)?;
                let mut prefix_open = true;
                for entry in log.iter()? {
                    let entry = entry
                        .map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
                    let ordinal = entry.0.value();
                    let record = decode_commit_record(entry.1.value())?;
                    if prefix_open && record.height < height {
                        let hc_key = CommitRecord::height_creator_key(
                            record.height,
                            &record.creator,
                            ordinal,
                        );
                        doomed.push(Doomed {
                            ordinal,
                            receipt_hash: record.receipt_hash,
                            turn_hash: record.turn_hash,
                            hc_key,
                            block_id: record.block_id,
                        });
                        doomed_records.push(record);
                    } else {
                        // First record at/above `height` closes the prefix; it
                        // and everything after it survive.
                        prefix_open = false;
                        survivors.push(record);
                    }
                }
            }

            compacted = u64::try_from(doomed.len()).map_err(|_| {
                StoreError::Integrity("compacted record count does not fit u64".to_string())
            })?;
            if compacted == 0 {
                // Nothing to do — leave the store (and its cursor) untouched.
                drop(write_txn);
                return Ok(0);
            }

            // Preserve the last writer for every compacted touched/tombstoned
            // id BEFORE deleting the only remaining copy of those write sets.
            // The current map stays unchanged; only its reconstruction layer
            // moves from live suffix to compacted baseline.
            crate::per_cell_receipt_heads::fold_compacted_per_cell_receipt_heads_in(
                &write_txn,
                old_floor,
                &doomed_records,
            )?;

            // Preserve the complete authority tuple and exact PoA sidecar identities BEFORE the
            // generic rows which authenticated them are removed. The certificate chain and its
            // terminal head advance in this same writer; a failure leaves the old log/floor intact.
            let checkpoint_identity = crate::poa_compact_authority::checkpoint_identity_in_write(
                &write_txn,
                checkpoint_height,
            )?;
            crate::poa_compact_authority::stage_compacted_commit_authority_prefix_in(
                &write_txn,
                old_floor,
                checkpoint_identity,
                &doomed_records,
                anchor,
            )?;

            // 2. Remove the doomed records from the commit log + their receipt /
            //    turn / (height, creator) index entries.
            {
                let mut log = write_txn.open_table(tables::COMMIT_LOG)?;
                let mut idx_receipt = write_txn.open_table(tables::IDX_RECEIPT_BY_HASH)?;
                let mut idx_turn = write_txn.open_table(tables::IDX_TURN_BY_HASH)?;
                let mut idx_hc = write_txn.open_table(tables::IDX_TURN_BY_HEIGHT_CREATOR)?;
                let mut compacted_ids = write_txn.open_table(tables::COMMIT_COMPACTED_BLOCK_IDS)?;
                for d in &doomed {
                    log.remove(d.ordinal)?;
                    idx_receipt.remove(&d.receipt_hash)?;
                    idx_turn.remove(&d.turn_hash)?;
                    idx_hc.remove(d.hc_key.as_slice())?;
                    // Carry the applied turn's id forward (no double-apply).
                    compacted_ids.insert(&d.block_id, ())?;
                }
            }

            // 3. Re-derive the cell-by-id index from the SURVIVORS alone
            //    (last-writer-wins). A cell whose only/latest writer was
            //    compacted drops out of the index — correct: the checkpoint
            //    now holds it, and the cell index is exactly the deltas ABOVE
            //    the checkpoint. This keeps the audit's cell-projection check
            //    exact post-compaction.
            {
                let mut idx_cell = write_txn.open_table(tables::IDX_CELL_BY_ID)?;
                let keys: Vec<[u8; 32]> = idx_cell
                    .iter()?
                    .filter_map(|e| e.ok().map(|e| *e.0.value()))
                    .collect();
                for k in keys {
                    idx_cell.remove(&k)?;
                }
                // Survivors are already in ascending ordinal order → later
                // writers/removals overwrite earlier ones (last-writer-wins).
                for record in &survivors {
                    for cell in &record.touched_cells {
                        let cell_bytes = postcard::to_stdvec(cell)
                            .map_err(|e| StoreError::Serialization(e.to_string()))?;
                        idx_cell.insert(&cell.id().0, cell_bytes.as_slice())?;
                    }
                    // A survivor that REMOVED a cell drops it from the index (a
                    // later removal wins over an earlier survivor's upsert).
                    for id in &record.removed {
                        idx_cell.remove(id)?;
                    }
                }
            }

            // 4. Advance the compaction floor by exactly the count removed.
            //    The commit CURSOR is deliberately UNTOUCHED — it is the applied
            //    high-water mark, not the physical record count.
            {
                let mut meta = write_txn.open_table(tables::METADATA)?;
                let new_floor = old_floor.checked_add(compacted).ok_or_else(|| {
                    StoreError::Integrity("commit-log compaction floor overflow".to_string())
                })?;
                meta.insert(tables::META_COMMIT_COMPACTED, new_floor)?;
            }
        }
        write_txn.commit()?;
        tracing::info!(
            requested_height = height,
            checkpoint_height,
            compacted,
            "compacted commit-log records subsumed by a covering ledger checkpoint"
        );
        Ok(compacted)
    }

    // =========================================================================
    // Crash recovery: recover-to-last-consistent (never strand a divergent image)
    // =========================================================================

    /// Find the highest commit ordinal whose reconstructed ledger root matches
    /// the root that record durably claims, TRUNCATE every divergent record past
    /// it, and return how many records were dropped (0 ⇒ the image was already
    /// consistent — a no-op).
    ///
    /// # Why this exists
    ///
    /// The boot-recovery convergence check (`starbridge-v2::persistence::recover`,
    /// node `state.rs`) reconstructs `checkpoint ⊕ overlay` and asserts the
    /// resulting canonical root equals the root the LAST committed turn recorded
    /// ([`Self::recovered_ledger_root`]). A torn or poisoned write — a process
    /// killed between the input-turn config write and the commit-record txn, a
    /// genesis-path mutation recorded over a turn-touched cell, or a second writer
    /// tearing the same file — leaves the log's tail inconsistent with that
    /// recorded root, and the check refuses the whole image. That STRANDS the
    /// owner: a divergent tail makes the entire durable session unopenable.
    ///
    /// Recovery is the right answer, not refusal. Each [`CommitRecord`] carries
    /// its OWN post-state root (`ledger_root`), so the log is self-checking at
    /// every ordinal: reconstructing `checkpoint ⊕ overlay[..=k]` and comparing to
    /// `record[k].ledger_root` decides whether the prefix through `k` is internally
    /// consistent. This walks the live log in ordinal order, tracks the last `k`
    /// that converges, and TRUNCATES `(k, cursor)` — dropping the divergent tail —
    /// so the image opens at the last-good state and the convergence check then
    /// PASSES at the recovered point. The recovery model is unchanged for the
    /// surviving prefix (`CrashRecovery.recover_eq_replay`): we only discard turns
    /// whose durable post-state cannot be reproduced, which were never safely
    /// committed in the first place.
    ///
    /// # The canonical-root contract
    ///
    /// The per-prefix root MUST be computed with the SAME commitment the records
    /// were written under ([`crate::canonical_ledger_root`], the `v2` whole-cell
    /// Merkle), so a reconstructed prefix is compared byte-for-byte against the
    /// recorded `ledger_root`. The reconstruction is `checkpoint` (the records at
    /// or below the latest checkpoint height are already folded in) plus the
    /// last-writer-wins overlay of every record's `touched_cells` applied in
    /// ordinal order — identical to [`Self::recover`]'s reconstruction, evaluated
    /// at every step instead of only the head.
    ///
    /// # Atomicity
    ///
    /// The truncation (remove the doomed records, drop their index entries, reset
    /// the cursor, re-derive the cell index from survivors) runs in ONE redb
    /// transaction. A crash mid-truncation leaves the pre-recovery (still
    /// divergent-but-untouched) store in place, so recovery is itself idempotent
    /// and crash-safe: re-running it reaches the same last-good point.
    ///
    /// Returns the number of divergent records truncated (0 ⇒ already consistent).
    ///
    /// # A mismatch in the MIDDLE is refused, not recovered (F3)
    ///
    /// A crash tears a SUFFIX. When the walk finds an ordinal `k` that misses its
    /// recorded root and a later ordinal `j` that reaches its own, the damage is
    /// inside the committed prefix — a corrupted `ledger_root` at `k`, or a
    /// corrupted `touched_cells` at `k` that `j` later overwrites — and no
    /// truncation can remove it without also removing `j`. The walk returns
    /// [`StoreError::IntermediateRootMismatch`] naming `k`, and truncates
    /// nothing. Until 2026-09-30 it remembered only `last_good` and returned
    /// `Ok(0)` whenever the head converged, so such an image opened as clean.
    ///
    /// That comparison is only as good as the reconstruction base, so it is made
    /// only for records the base can actually reproduce: those ABOVE the latest
    /// ledger checkpoint's height (below it the running ledger is the checkpoint,
    /// which already folds in later records), and only when the base is
    /// complete — a checkpoint exists, or the caller supplied its genesis
    /// baseline through [`Self::recover_to_last_consistent_from_base`]. With an
    /// EMPTY base and no checkpoint, every untouched genesis cell is missing and a
    /// mismatch followed by a match is what an honest image looks like once the
    /// last genesis cell has been touched; that walk stays inconclusive, as the
    /// node's boot path already treats it.
    pub fn recover_to_last_consistent(&self) -> Result<u64> {
        // No genesis baseline: the reconstruction starts from the latest
        // checkpoint, or an EMPTY ledger when none exists. Correct for a store
        // whose every cell was established by a committed turn (e.g. a starbridge
        // World) — there are no UNTOUCHED genesis cells to restore. A node with a
        // genesis baseline (fee/issuer wells, faucet) must use
        // [`Self::recover_to_last_consistent_from_base`] instead.
        self.recover_walk(&dregg_cell::Ledger::new(), false)
    }

    /// [`Self::recover_to_last_consistent`] reconstructing on top of an explicit
    /// genesis BASELINE instead of an empty ledger when no checkpoint exists.
    ///
    /// # Why a baseline is required for sub-checkpoint recovery
    ///
    /// A node that finalized turns BELOW its first ledger checkpoint has no
    /// checkpoint to restore its UNTOUCHED genesis cells from (the fee well, the
    /// issuer well, a faucet — cells genesis established but no turn has touched).
    /// The commit-log overlay carries ONLY the cells a turn touched, so
    /// reconstructing from an empty base yields the touched-cell delta, NOT the
    /// full finalized ledger. But every record's `ledger_root` commits the FULL
    /// ledger (genesis ⊕ touched). Comparing the delta's root against that claim
    /// mismatches at EVERY ordinal, so the no-baseline walk finds NO converging
    /// prefix and refuses a perfectly recoverable image as unsalvageable — a
    /// FALSE store-integrity fatal on an abrupt power loss, exactly the
    /// sub-checkpoint power-cycle that wedges a whole-cluster restart.
    ///
    /// Seeding `base` (the genesis baseline) first mirrors the node's
    /// `reseed_genesis_then_overlay` recovery order — genesis baseline, the latest
    /// checkpoint laid over it, then the commit-log overlay last-writer-wins — so
    /// a torn tail recovers cleanly to the last root-converging ordinal while a
    /// GENUINE divergence (no prefix reconstructs to its recorded root even with
    /// the baseline in place) still fails closed. `base` empty reproduces
    /// [`Self::recover_to_last_consistent`] exactly.
    ///
    /// The caller asserts `base` is the COMPLETE pre-log baseline, so every
    /// record above the checkpoint is checkable and an intermediate mismatch is
    /// refused (see [`Self::recover_to_last_consistent`]).
    pub fn recover_to_last_consistent_from_base(&self, base: &dregg_cell::Ledger) -> Result<u64> {
        self.recover_walk(base, true)
    }

    /// The torn-tail walk. `base_is_complete`: the caller vouches that `base`
    /// holds every cell the log's roots commit that no record touches.
    fn recover_walk(&self, base: &dregg_cell::Ledger, base_is_complete: bool) -> Result<u64> {
        let floor = self.commit_compacted_floor()?;
        let cursor = self.commit_cursor()?;
        if cursor <= floor {
            // No live records to check (fresh or fully compacted) — nothing to do.
            return Ok(0);
        }

        // Reconstruction base: the genesis BASELINE first, with the latest full
        // ledger checkpoint laid OVER it. A checkpoint is a full snapshot that
        // normally already carries genesis; laying it over `base` also restores
        // any untouched genesis cell a sub-checkpoint store has no checkpoint for.
        // The checkpoint folds in every record at/below its height; the live
        // overlay re-asserts post-checkpoint cells last-writer-wins. We walk the
        // SAME reconstruction `recover` uses (genesis ⊕ checkpoint ⊕ overlay),
        // evaluating the canonical root after EACH record so we find the last
        // ordinal that converges to its claim.
        let mut ledger = base.clone();
        let mut checkpoint_height: Option<u64> = None;
        if let Some((height, checkpoint)) = self.load_latest_ledger_checkpoint()? {
            checkpoint_height = Some(height);
            for (_, cell) in checkpoint.iter() {
                let _ = ledger.remove(&cell.id());
                let _ = ledger.insert_cell(cell.clone());
            }
        }
        // Can a mismatch followed by a match be told apart from an incomplete
        // base? Only when the base is complete: a checkpoint (a full snapshot)
        // or a caller-vouched genesis baseline.
        let intermediate_checked = base_is_complete || checkpoint_height.is_some();

        // Scan the live log in ordinal order, applying each record's touched cells
        // and remembering the last ordinal whose running root matches its claim —
        // and the FIRST checkable ordinal that misses, which is fatal the moment
        // any later checkable ordinal converges.
        let mut last_good: Option<u64> = None;
        let mut first_miss: Option<(u64, u64)> = None;
        {
            let read_txn = self.db.begin_read()?;
            let log = read_txn.open_table(tables::COMMIT_LOG)?;
            for entry in log.range(floor..)? {
                let entry =
                    entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
                let ordinal = entry.0.value();
                let record = decode_commit_record(entry.1.value())?;
                // Apply this record's touched cells last-writer-wins. A record above
                // the checkpoint contributes the overlay; one at/below it merely
                // re-asserts cells the checkpoint already folded in (idempotent —
                // same id, same post-state). Either way, after applying this record
                // the ledger is the finalized state as of this turn, so its root is
                // comparable to the record's recorded `ledger_root`.
                for cell in &record.touched_cells {
                    let _ = ledger.remove(&cell.id());
                    let _ = ledger.insert_cell(cell.clone());
                }
                // Apply this record's tombstones (MakeSovereign) as deletions, in
                // ordinal order, so the running root matches the finalized root a
                // record that removed a cell recorded (else the prefix would never
                // converge and a recoverable image would be falsely truncated).
                for id in &record.removed {
                    let _ = ledger.remove(&CellId(*id));
                }
                // Above the checkpoint the running ledger IS this record's
                // post-state; at or below it, the ledger is the checkpoint (which
                // already holds later records), so a miss there says nothing.
                let checkable =
                    intermediate_checked && checkpoint_height.is_none_or(|h| record.height > h);
                if crate::canonical_ledger_root(&ledger) == record.ledger_root {
                    if checkable && let Some((ordinal_missed, height)) = first_miss {
                        return Err(StoreError::IntermediateRootMismatch {
                            ordinal: ordinal_missed,
                            height,
                            converged_at: ordinal,
                        });
                    }
                    last_good = Some(ordinal);
                } else if checkable && first_miss.is_none() {
                    first_miss = Some((ordinal, record.height));
                }
            }
        }

        // The new cursor: one past the last converging ordinal. If NOTHING
        // converged, the entire live log is divergent — there is no salvageable
        // last-good point in the records (the caller must start fresh; we do not
        // silently empty the log here, that is the caller's explicit choice).
        let Some(last_good) = last_good else {
            return Err(StoreError::Integrity(
                "recover_to_last_consistent: NO commit-log prefix reconstructs to its recorded \
                 root — the image cannot be salvaged to a last-good point (start fresh)"
                    .to_string(),
            ));
        };
        let new_cursor = last_good + 1;
        if new_cursor == cursor {
            // The head already converges — the image is consistent, no tear.
            return Ok(0);
        }

        self.truncate_commit_tail(cursor, new_cursor, None)
    }

    /// Remove only a suffix outside a caller-validated publication journal.
    /// The caller must first validate its entire published prefix. The durable
    /// journal head, current cursor and retained receipt are compared inside the
    /// same transaction as every log/index/admission cleanup, so a concurrent
    /// publication cannot be mistaken for an unpublished suffix.
    pub fn truncate_unpublished_tail(
        &self,
        expected_cursor: u64,
        retained_cursor: u64,
        retained_receipt: Option<[u8; 32]>,
        publication_key: &str,
        publication_bytes: &[u8],
    ) -> Result<u64> {
        self.truncate_commit_tail(
            expected_cursor,
            retained_cursor,
            Some((retained_receipt, publication_key, publication_bytes)),
        )
    }

    fn truncate_commit_tail(
        &self,
        cursor: u64,
        new_cursor: u64,
        publication_guard: Option<(Option<[u8; 32]>, &str, &[u8])>,
    ) -> Result<u64> {
        // Rewrites the commit log / per-cell head tables beyond an append.
        let _rewrite = self.per_cell_head_cache.begin_rewrite();
        // ── TRUNCATE the divergent tail `(new_cursor, cursor)` in ONE txn ──────
        let write_txn = self.db.begin_write()?;
        let floor;
        {
            let metadata = write_txn.open_table(tables::METADATA)?;
            let actual_cursor = metadata
                .get(tables::META_COMMIT_CURSOR)?
                .map(|value| value.value())
                .unwrap_or(0);
            floor = metadata
                .get(tables::META_COMMIT_COMPACTED)?
                .map(|value| value.value())
                .unwrap_or(0);
            if actual_cursor != cursor || new_cursor < floor || new_cursor > cursor {
                return Err(StoreError::Integrity(
                    "commit tail changed or requested prefix is outside the live log".to_string(),
                ));
            }
        }
        if let Some((expected_receipt, config_key, expected_config)) = publication_guard {
            let actual_receipt = if new_cursor == 0 {
                None
            } else {
                let log = write_txn.open_table(tables::COMMIT_LOG)?;
                let row = log.get(new_cursor - 1)?.ok_or_else(|| {
                    StoreError::Integrity("retained publication receipt is missing".to_string())
                })?;
                Some(decode_commit_record(row.value())?.receipt_hash)
            };
            if actual_receipt != expected_receipt {
                return Err(StoreError::Integrity(
                    "retained publication receipt changed".to_string(),
                ));
            }
            let config = write_txn.open_table(tables::METADATA_BYTES)?;
            if config
                .get(config_key)?
                .map(|value| value.value() == expected_config)
                != Some(true)
            {
                return Err(StoreError::Integrity(
                    "ordered publication head changed before tail recovery".to_string(),
                ));
            }
        }
        let truncated;
        {
            // Collect doomed records (their index keys) so we can clean the index.
            struct Doomed {
                ordinal: u64,
                receipt_hash: [u8; 32],
                turn_hash: [u8; 32],
                hc_key: [u8; 48],
            }
            let mut doomed: Vec<Doomed> = Vec::new();
            {
                let log = write_txn.open_table(tables::COMMIT_LOG)?;
                for entry in log.range(new_cursor..)? {
                    let entry = entry
                        .map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
                    let ordinal = entry.0.value();
                    let record = decode_commit_record(entry.1.value())?;
                    let hc_key =
                        CommitRecord::height_creator_key(record.height, &record.creator, ordinal);
                    doomed.push(Doomed {
                        ordinal,
                        receipt_hash: record.receipt_hash,
                        turn_hash: record.turn_hash,
                        hc_key,
                    });
                }
            }
            truncated = doomed.len() as u64;

            // Remove the doomed records + their receipt / turn / (h,c) index entries.
            {
                let mut log = write_txn.open_table(tables::COMMIT_LOG)?;
                let mut idx_receipt = write_txn.open_table(tables::IDX_RECEIPT_BY_HASH)?;
                let mut idx_turn = write_txn.open_table(tables::IDX_TURN_BY_HASH)?;
                let mut idx_hc = write_txn.open_table(tables::IDX_TURN_BY_HEIGHT_CREATOR)?;
                for d in &doomed {
                    log.remove(d.ordinal)?;
                    idx_receipt.remove(&d.receipt_hash)?;
                    idx_turn.remove(&d.turn_hash)?;
                    idx_hc.remove(d.hc_key.as_slice())?;
                }
            }

            let survivors: Vec<CommitRecord> = {
                let log = write_txn.open_table(tables::COMMIT_LOG)?;
                let mut v = Vec::new();
                for entry in log.range(floor..)? {
                    let entry = entry
                        .map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
                    v.push(decode_commit_record(entry.1.value())?);
                }
                v
            };

            // Re-derive the cell-by-id index from the SURVIVING records alone
            // (last-writer-wins) — a cell whose only/latest writer was truncated
            // drops to its checkpoint value (handled on the next recover overlay).
            {
                let mut idx_cell = write_txn.open_table(tables::IDX_CELL_BY_ID)?;
                let keys: Vec<[u8; 32]> = idx_cell
                    .iter()?
                    .filter_map(|e| e.ok().map(|e| *e.0.value()))
                    .collect();
                for k in keys {
                    idx_cell.remove(&k)?;
                }
                for record in &survivors {
                    for cell in &record.touched_cells {
                        let cell_bytes = postcard::to_stdvec(cell)
                            .map_err(|e| StoreError::Serialization(e.to_string()))?;
                        idx_cell.insert(&cell.id().0, cell_bytes.as_slice())?;
                    }
                    for removed in &record.removed {
                        idx_cell.remove(removed)?;
                    }
                }
            }

            // Roll generic per-cell provenance back over the same survivor
            // image. The compacted baseline is indispensable here: a doomed
            // live writer may have a predecessor whose record no longer exists.
            crate::per_cell_receipt_heads::rebuild_current_per_cell_receipt_heads_in(
                &write_txn, floor, new_cursor, &survivors,
            )?;

            // Regress every tracked executor-owned admission/root table to the
            // same last-good ordinal before publishing the lower cursor. This
            // includes typed commitment/revocation records, inbound bridge
            // burns, sparse rate snapshots, positional note leaves, and caches.
            crate::executor_consensus_state::truncate_executor_consensus_state_in(
                &write_txn, new_cursor,
            )?;

            crate::poa_signal_state::truncate_poa_signal_state_in(&write_txn, new_cursor)?;
            crate::poa_event_store::truncate_poa_event_store_in(&write_txn, new_cursor)?;
            crate::poa_event_batch_v2::truncate_poa_event_batch_store_v2_in(
                &write_txn, new_cursor,
            )?;
            crate::poa_holding_consumption::truncate_poa_holding_consumptions_in(
                &write_txn, new_cursor,
            )?;

            // Reset the durable cursor to the last-good high-water mark. Unlike
            // compaction (which leaves the cursor as the applied high-water mark),
            // a truncated turn was NEVER safely applied, so the cursor REGRESSES to
            // the last-good ordinal + 1 — the recovered applied count.
            {
                let mut meta = write_txn.open_table(tables::METADATA)?;
                meta.insert(tables::META_COMMIT_CURSOR, new_cursor)?;
            }
        }
        write_txn.commit()?;
        tracing::warn!(
            cursor,
            new_cursor,
            truncated,
            "truncated a guarded unpublished or root-divergent commit-log tail"
        );
        Ok(truncated)
    }

    /// One-time migration: the `(height, creator)` index key gained a trailing
    /// ordinal (40 → 48 bytes) when route-level turns started committing to
    /// the log (several can share a `(height, creator)` pair). A store written
    /// by an older node carries 40-byte keys; rebuilding the index from the
    /// log (the source of truth) re-derives every entry in the new shape.
    /// Called from [`PersistentStore::open`]; a no-op on already-migrated and
    /// fresh stores.
    pub(crate) fn migrate_height_creator_index(&self) -> Result<()> {
        let needs_migration = {
            let read_txn = self.db.begin_read()?;
            let idx_hc = read_txn.open_table(tables::IDX_TURN_BY_HEIGHT_CREATOR)?;
            let mut found_legacy = false;
            for entry in idx_hc.iter()? {
                let entry =
                    entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
                if entry.0.value().len() != 48 {
                    found_legacy = true;
                    break;
                }
            }
            found_legacy
        };
        if needs_migration {
            let replayed = self.rebuild_index_from_log()?;
            tracing::info!(
                replayed,
                "migrated turn_by_height_creator index to the (height, creator, ordinal) key shape"
            );
        }
        Ok(())
    }
}

// =============================================================================
// Internal helpers
// =============================================================================

fn check_hash_index(
    index: &impl ReadableTable<&'static [u8; 32], u64>,
    key: &[u8; 32],
    ordinal: u64,
    name: &str,
    report: &mut IndexAuditReport,
) -> Result<()> {
    match index.get(key)? {
        Some(g) if g.value() == ordinal => {}
        Some(g) => report.mismatched_entries.push(format!(
            "{name}({}) -> {} but record at ordinal {ordinal}",
            hex32(key),
            g.value()
        )),
        None => report.missing_entries.push(format!(
            "{name}({}) missing for ordinal {ordinal}",
            hex32(key)
        )),
    }
    Ok(())
}

fn check_no_orphans(
    index: &impl ReadableTable<&'static [u8; 32], u64>,
    log: &impl ReadableTable<u64, &'static [u8]>,
    name: &str,
    report: &mut IndexAuditReport,
) -> Result<()> {
    for entry in index.iter()? {
        let entry = entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
        let ordinal = entry.1.value();
        if log.get(ordinal)?.is_none() {
            report
                .orphan_entries
                .push(format!("{name} -> missing ordinal {ordinal}"));
        }
    }
    Ok(())
}

fn clear_table_u32(
    txn: &redb::WriteTransaction,
    def: redb::TableDefinition<&'static [u8; 32], u64>,
) -> Result<()> {
    let mut table = txn.open_table(def)?;
    let keys: Vec<[u8; 32]> = table
        .iter()?
        .filter_map(|e| e.ok().map(|e| *e.0.value()))
        .collect();
    for k in keys {
        table.remove(&k)?;
    }
    Ok(())
}

fn hex32(b: &[u8; 32]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
// `pub(crate)` so sibling modules' tests can build their stores through the PRODUCTION
// finalized-turn apparatus that lives here — see `commit_test_exact_frame_turn`.
pub(crate) mod tests {
    use super::*;
    use crate::PersistentStore;
    use dregg_cell::Cell;
    use ed25519_dalek::Signer as _;
    use sha2::{Digest as _, Sha256};

    struct FaithfulSigner {
        ed: dregg_types::SigningKey,
        ed_pk: PublicKey,
        pq_pk: MlDsaPublicKey,
        pq: dregg_federation::frost::MlDsaSigningKey,
    }

    impl FaithfulSigner {
        fn new(seed: u8) -> Self {
            // The ML-DSA-65 derivation below goes through `dregg-pq`, which aborts the process
            // with no verified core installed — see `FaithfulNoteRootEnvelopeV1::verify_hybrid`.
            dregg_pq_testkit::install_or_panic();
            let bytes = [seed; 32];
            let ed = dregg_types::SigningKey::from_bytes(&bytes);
            let ed_pk = ed.public_key();
            let (pq_pk, pq) = dregg_federation::frost::MlDsaSigningKey::from_seed(&bytes);
            Self {
                ed,
                ed_pk,
                pq_pk,
                pq,
            }
        }

        fn sign_edge(&self, edge: crate::FaithfulNoteRootRecordV1) -> FaithfulNoteRootEnvelopeV1 {
            let message = edge.signing_message();
            FaithfulNoteRootEnvelopeV1 {
                record: edge,
                hybrid_quorum: vec![dregg_types::HybridQuorumSig {
                    pubkey: self.ed_pk,
                    signature: dregg_types::sign(&self.ed, &message),
                    ml_dsa_pubkey: self.pq_pk.0.to_vec(),
                    pq_signature: self.pq.sign(&message).expect("ML-DSA signs"),
                }],
            }
        }

        fn sign_attested(&self, mut root: StoredAttestedRoot) -> StoredAttestedRoot {
            let signature = dregg_types::sign(&self.ed, &root.signing_message());
            root.quorum_signatures = vec![(self.ed_pk, signature)];
            root
        }
    }

    fn faithful_context() -> ([u8; 32], [u8; 32]) {
        ([0x51; 32], [0x52; 32])
    }

    fn plan_test_edge(
        store: &PersistentStore,
        height: u64,
        block_id: [u8; 32],
        new_commitments: &[[u8; 32]],
    ) -> (FaithfulNoteRootAnchorV1, crate::FaithfulNoteRootRecordV1) {
        let commitments: Vec<[u8; 32]> = store
            .load_all_note_commitments()
            .unwrap()
            .into_iter()
            .map(|commitment| commitment.0)
            .collect();
        let tree = Poseidon2NoteTree::from_blake3_commitments(&commitments, LIVE_NOTE_TREE_DEPTH);
        let (session, federation) = faithful_context();
        let anchor = store.faithful_note_root_head().unwrap().unwrap_or_else(|| {
            FaithfulNoteRootAnchorV1::new(
                session,
                federation,
                9,
                height - 1,
                u64::try_from(tree.size()).unwrap(),
                crate::CanonicalFaithfulRoot::from_faithful(tree.faithful_root_immutable()),
            )
            .unwrap()
        });
        let edge =
            crate::plan_faithful_note_root_transition_v1(&tree, &anchor, block_id, new_commitments)
                .unwrap();
        (anchor, edge)
    }

    fn test_finalized_spend_inputs(
        store: &PersistentStore,
        historical: &FaithfulNoteRootAnchorV1,
        spends: &[FinalizedNullifierRecord],
    ) -> Vec<crate::FinalizedFaithfulSpendInput> {
        let records = store.load_faithful_nullifier_records().unwrap();
        let mut set = dregg_cell::nullifier_set::NullifierSet::from_records(records).unwrap();
        spends
            .iter()
            .enumerate()
            .map(|(index, spend)| {
                set.insert(dregg_cell::note::Nullifier(spend.nullifier), spend.value)
                    .unwrap();
                crate::FinalizedFaithfulSpendInput {
                    root_height: historical.height,
                    historical_note_root: historical.root,
                    nullifier: spend.nullifier,
                    value: spend.value,
                    asset_type: 0x7000 + u64::try_from(index).unwrap(),
                    successor_nullifier_root: crate::CanonicalFaithfulRoot::from_faithful(
                        set.root8(),
                    ),
                }
            })
            .collect()
    }

    fn test_attested(
        signer: &FaithfulSigner,
        record: &CommitRecord,
        edge: &crate::FaithfulNoteRootRecordV1,
    ) -> StoredAttestedRoot {
        signer.sign_attested(StoredAttestedRoot {
            merkle_root: record.ledger_root,
            note_tree_root: Some(edge.successor.to_bytes()),
            nullifier_set_root: Some(
                dregg_cell::nullifier_set::NullifierSet::new()
                    .root8()
                    .to_bytes32(),
            ),
            height: record.height,
            timestamp: 1_700_000_000,
            blocklace_block_id: Some(record.block_id),
            finality_round: Some(record.height),
            quorum_signatures: Vec::new(),
            threshold_qc: None,
            threshold: 1,
            federation_id: dregg_types::FederationId(edge.federation_id),
            receipt_stream_root: Some([0x61; 32]),
            finalization_quorum: Vec::new(),
        })
    }

    fn test_attested_with_nullifier_root(
        signer: &FaithfulSigner,
        record: &CommitRecord,
        edge: &crate::FaithfulNoteRootRecordV1,
        nullifier_root: [u8; 32],
    ) -> StoredAttestedRoot {
        let mut attested = test_attested(signer, record, edge);
        attested.nullifier_set_root = Some(nullifier_root);
        signer.sign_attested(attested)
    }

    fn faithful_commit_record(ordinal: u64, block_id: [u8; 32]) -> CommitRecord {
        let mut out = record(ordinal, ordinal, Vec::new());
        out.height = ordinal + 1;
        out.block_id = block_id;
        out.turn_hash = [0x70 + ordinal as u8; 32];
        out.receipt_hash = [0x80 + ordinal as u8; 32];
        out.ledger_root = [0x90 + ordinal as u8; 32];
        out
    }

    struct GalleyFaithfulFixture {
        signer: FaithfulSigner,
        initial_anchor: Option<FaithfulNoteRootAnchorV1>,
        envelope: FaithfulNoteRootEnvelopeV1,
        attested: StoredAttestedRoot,
        spent: Vec<FinalizedNullifierRecord>,
        finalized_spends: Vec<crate::FinalizedFaithfulSpendInput>,
    }

    impl GalleyFaithfulFixture {
        fn weld(&self) -> FinalizedFaithfulRootWeld<'_> {
            FinalizedFaithfulRootWeld {
                initial_anchor: self.initial_anchor.as_ref(),
                envelope: &self.envelope,
                author_committee: std::slice::from_ref(&self.signer.ed_pk),
                author_ml_dsa_committee: std::slice::from_ref(&self.signer.pq_pk),
                attested_root: &self.attested,
                spent_nullifiers: &self.spent,
                finalized_spends: &self.finalized_spends,
            }
        }
    }

    fn galley_faithful_fixture(
        store: &PersistentStore,
        record: &CommitRecord,
        spend_seed: Option<u8>,
    ) -> GalleyFaithfulFixture {
        let signer = FaithfulSigner::new(0x76);
        let fresh_segment = store
            .faithful_note_root_head()
            .expect("faithful head")
            .is_none();
        let (anchor, edge) = plan_test_edge(store, record.height, record.block_id, &[]);
        let envelope = signer.sign_edge(edge.clone());
        let spent = spend_seed
            .map(|seed| {
                vec![FinalizedNullifierRecord {
                    nullifier: [seed; 32],
                    value: u64::from(seed),
                }]
            })
            .unwrap_or_default();
        let finalized_spends = test_finalized_spend_inputs(store, &anchor, &spent);
        let attested = if spent.is_empty() {
            test_attested(&signer, record, &edge)
        } else {
            let successor = store
                .plan_faithful_nullifier_successor(&spent)
                .expect("faithful nullifier successor");
            test_attested_with_nullifier_root(&signer, record, &edge, successor)
        };
        GalleyFaithfulFixture {
            signer,
            initial_anchor: fresh_segment.then_some(anchor),
            envelope,
            attested,
            spent,
            finalized_spends,
        }
    }

    fn galley_hex(bytes: [u8; 32]) -> String {
        bytes.iter().map(|byte| format!("{byte:02x}")).collect()
    }

    fn galley_world(root: u8) -> crate::PoaWorldIdentityV2 {
        crate::PoaWorldIdentityV2::new([2; 32], [root; 32], [0x52; 32], [0x53; 32], 7)
            .expect("Galley world")
    }

    fn galley_policy_json() -> Vec<u8> {
        format!(
            "{{\"deployment_id\":\"{}\",\"federation_id\":\"{}\",\"daily_id\":\"{}\",\"genesis_head\":\"{}\",\"dregg_mint\":5,\"snapshot_slot\":6,\"content_epoch\":7,\"event_id\":\"{}\",\"rules_digest\":\"{}\",\"public_activity_id\":\"{}\",\"scene_content_id\":\"{}\",\"public_action_content_id\":\"{}\",\"sponsor_action_content_id\":\"{}\",\"complete_content_id\":\"{}\",\"public_service\":3,\"sponsor_service\":2,\"service_target\":10,\"power_root\":\"{}\",\"loot_root\":\"{}\",\"canon_root\":\"{}\",\"canon_revision\":18}}",
            galley_hex([1; 32]),
            galley_hex([2; 32]),
            galley_hex([3; 32]),
            galley_hex([4; 32]),
            galley_hex([9; 32]),
            galley_hex([10; 32]),
            galley_hex([10; 32]),
            galley_hex([11; 32]),
            galley_hex([12; 32]),
            galley_hex([13; 32]),
            galley_hex([14; 32]),
            galley_hex([15; 32]),
            galley_hex([16; 32]),
            galley_hex([17; 32]),
        )
        .into_bytes()
    }

    fn galley_genesis_projection_json() -> Vec<u8> {
        format!(
            "{{\"sequence\":0,\"public_players\":[],\"sponsors\":[],\"spent_grant_nullifiers\":[],\"public_play_count\":0,\"sponsorship_count\":0,\"local_service_total\":0,\"power_root\":\"{}\",\"loot_root\":\"{}\",\"canon_root\":\"{}\",\"canon_revision\":18}}",
            galley_hex([15; 32]),
            galley_hex([16; 32]),
            galley_hex([17; 32]),
        )
        .into_bytes()
    }

    fn galley_policy(world: crate::PoaWorldIdentityV2) -> crate::AuthenticatedPoaGalleyPolicyV1 {
        crate::AuthenticatedPoaGalleyPolicyV1::from_verified_content_inclusion(
            world,
            galley_policy_json(),
            galley_genesis_projection_json(),
        )
        .expect("authenticated Galley policy fixture")
    }

    /// ⚑ **ARMED GUARD** (2026-08-08). Absent export ⇒ `demand_lean` PANICS naming the capability.
    ///
    /// These eight call sites are the Galley commit-adapter and raw-apex refusal tests —
    /// `..._rejects_invalid_signature_after_staging_and_rolls_back`,
    /// `..._refuses_replay_invention_...`, `..._wrong_current_world_rolls_back_every_weld`. Every
    /// one of them used to `return` silently on an absent archive and report `ok`, which is the
    /// same object as a deleted test. See the note on `poa_world_activation::tests::require_native`.
    fn galley_native_available() -> bool {
        dregg_lean_ffi::demand_lean(
            dregg_lean_ffi::poa_world_activation_ffi::poa_world_activation_available()
                && dregg_lean_ffi::poa_activated_content_ffi::poa_activated_content_runtime_available()
                && dregg_lean_ffi::poa_galley_ffi::poa_galley_daily_available()
                && dregg_lean_ffi::poa_event_batch_ffi::poa_event_batch_runtime_available()
                && dregg_lean_ffi::poa_event_batch_ffi::poa_event_batch_initial_heads_digest_available(),
            "the PoA Galley authority path (world-activation + activated-content + galley-daily + \
             event-batch runtime + initial-heads digest)",
        )
    }

    fn raw_galley_policy_json(epoch: u64, public_action: u8) -> String {
        format!(
            concat!(
                "{{\"deployment_id\":\"{}\",\"federation_id\":\"{}\",",
                "\"daily_id\":\"{}\",\"genesis_head\":\"{}\",\"dregg_mint\":5,",
                "\"snapshot_slot\":6,\"content_epoch\":{},\"event_id\":\"{}\",",
                "\"rules_digest\":\"{}\",\"public_activity_id\":\"{}\",",
                "\"scene_content_id\":\"{}\",\"public_action_content_id\":\"{}\",",
                "\"sponsor_action_content_id\":\"{}\",\"complete_content_id\":\"{}\",",
                "\"public_service\":3,\"sponsor_service\":2,\"service_target\":10,",
                "\"power_root\":\"{}\",\"loot_root\":\"{}\",\"canon_root\":\"{}\",",
                "\"canon_revision\":18}}"
            ),
            galley_hex([1; 32]),
            galley_hex([1; 32]),
            galley_hex([3; 32]),
            galley_hex([4; 32]),
            epoch,
            galley_hex([9; 32]),
            galley_hex([10; 32]),
            galley_hex([10; 32]),
            galley_hex([11; 32]),
            galley_hex([public_action; 32]),
            galley_hex([13; 32]),
            galley_hex([14; 32]),
            galley_hex([15; 32]),
            galley_hex([16; 32]),
            galley_hex([17; 32]),
        )
    }

    fn raw_galley_manifest_json(session: u8, epoch: u64, policy_json: &str) -> Vec<u8> {
        let policy_digest: [u8; 32] = Sha256::digest(policy_json.as_bytes()).into();
        let quoted_policy = serde_json::to_string(policy_json).expect("quoted Galley policy");
        format!(
            concat!(
                "{{\"format\":\"POA-ACTIVATED-CONTENT-MANIFEST-1\",",
                "\"scope\":{{\"federation_id\":\"{}\",\"content_session\":\"{}\",",
                "\"content_epoch\":{}}},\"legacy_whole_pack_sha256\":null,",
                "\"components\":[{{\"name\":\"poa.galley-maintenance-daily.policy.v1\",",
                "\"sha256\":\"{}\",\"bytes_utf8\":{}}}]}}"
            ),
            galley_hex([1; 32]),
            galley_hex([session; 32]),
            epoch,
            galley_hex(policy_digest),
            quoted_policy,
        )
        .into_bytes()
    }

    fn raw_galley_world_bundle(
        activation: u8,
        session: u8,
        epoch: u64,
        public_action: u8,
    ) -> (crate::PoaWorldIdentityV2, Vec<u8>) {
        let policy = raw_galley_policy_json(epoch, public_action);
        let manifest = raw_galley_manifest_json(session, epoch, &policy);
        let world = crate::PoaWorldIdentityV2::new(
            [1; 32],
            Sha256::digest(&manifest).into(),
            [activation; 32],
            [session; 32],
            epoch,
        )
        .expect("raw Galley world");
        (world, manifest)
    }

    fn install_raw_galley_world_and_content(
        store: &PersistentStore,
        world: crate::PoaWorldIdentityV2,
        manifest: Vec<u8>,
    ) {
        assert!(install_active_poa_world(store, world));
        store
            .install_poa_activated_content_v1(manifest)
            .expect("authenticated Galley content install");
    }

    fn advance_raw_galley_world_and_content(
        store: &PersistentStore,
        world: crate::PoaWorldIdentityV2,
        manifest: Vec<u8>,
    ) {
        advance_active_poa_world(store, world);
        store
            .install_poa_activated_content_v1(manifest)
            .expect("successor authenticated Galley content install");
    }

    fn raw_galley_signer_for(seed: u8) -> [u8; 32] {
        ed25519_dalek::SigningKey::from_bytes(&[seed; 32])
            .verifying_key()
            .to_bytes()
    }

    fn raw_galley_signer() -> [u8; 32] {
        raw_galley_signer_for(0x41)
    }

    fn raw_galley_player_cell_for(seed: u8) -> [u8; 32] {
        dregg_turn::poa_galley_carrier::galley_player_cell(&raw_galley_signer_for(seed)).0
    }

    fn raw_galley_player_cell() -> [u8; 32] {
        raw_galley_player_cell_for(0x41)
    }

    fn raw_galley_turn_material_for(
        world: &crate::PoaWorldIdentityV2,
        ordinal: u64,
        previous_receipt_hash: Option<[u8; 32]>,
        action_token: [u8; 32],
        action_content_id: [u8; 32],
        signer_seed: u8,
    ) -> (
        dregg_turn::SignedTurn,
        dregg_turn::TurnReceipt,
        CommitRecord,
    ) {
        let key = ed25519_dalek::SigningKey::from_bytes(&[signer_seed; 32]);
        let signer = dregg_types::PublicKey(key.verifying_key().to_bytes());
        let mut turn = dregg_turn::poa_galley_carrier::galley_player_command_turn(
            &signer.0,
            8 + ordinal,
            previous_receipt_hash,
            dregg_turn::poa_galley_carrier::GalleyPlayerCommandV1::Perform {
                action_token: dregg_turn::poa_galley_carrier::GalleyActionToken::from_bytes(
                    action_token,
                ),
                action_content_id,
            },
        );
        turn.call_forest.hash();
        let turn_hash = turn.hash();
        let signed = dregg_turn::SignedTurn {
            turn,
            signature: dregg_types::Signature(key.sign(&turn_hash).to_bytes()),
            signer,
            pq_signature: Vec::new(),
            pq_signer: Vec::new(),
        };
        let dregg_turn::Effect::EmitEvent { cell, event } =
            &signed.turn.call_forest.roots[0].action.effects[0]
        else {
            panic!("raw Galley fixture is an exact EmitEvent")
        };
        let effect_hash = signed.turn.call_forest.roots[0].action.effects[0].hash();
        let receipt = dregg_turn::TurnReceipt {
            turn_hash,
            forest_hash: signed.turn.call_forest.compute_hash(),
            pre_state_hash: [0x33_u8.wrapping_add(ordinal as u8); 32],
            post_state_hash: [0x43_u8.wrapping_add(ordinal as u8); 32],
            effects_hash: *blake3::hash(&effect_hash).as_bytes(),
            action_count: 1,
            previous_receipt_hash,
            agent: signed.turn.agent,
            federation_id: world.federation_id(),
            emitted_events: vec![dregg_turn::EmittedEvent {
                cell: *cell,
                topic: event.topic,
                data: event.data.clone(),
            }],
            finality: dregg_turn::Finality::Final,
            ..dregg_turn::TurnReceipt::default()
        };
        let mut record = faithful_commit_record(ordinal, [0x35_u8.wrapping_add(ordinal as u8); 32]);
        record.turn_hash = turn_hash;
        record.creator = signed.turn.agent.0;
        record.receipt_hash = receipt.receipt_hash();
        (signed, receipt, record)
    }

    fn raw_galley_turn_material(
        world: &crate::PoaWorldIdentityV2,
        ordinal: u64,
        previous_receipt_hash: Option<[u8; 32]>,
        action_token: [u8; 32],
        action_content_id: [u8; 32],
    ) -> (
        dregg_turn::SignedTurn,
        dregg_turn::TurnReceipt,
        CommitRecord,
    ) {
        raw_galley_turn_material_for(
            world,
            ordinal,
            previous_receipt_hash,
            action_token,
            action_content_id,
            0x41,
        )
    }

    fn galley_turn_material(
        world: crate::PoaWorldIdentityV2,
        ordinal: u64,
        previous_receipt_hash: Option<[u8; 32]>,
    ) -> (
        CommitRecord,
        Vec<u8>,
        crate::FinalizedTurnCoordinateV2,
        [u8; 32],
    ) {
        let signer = [0x65; 32];
        let actor_root = [0x64_u8.wrapping_add(ordinal as u8); 32];
        let player_cell =
            dregg_cell::CellId::derive_raw(&signer, blake3::hash(b"default").as_bytes()).0;
        let mut commit = faithful_commit_record(ordinal, [0x61_u8.wrapping_add(ordinal as u8); 32]);
        commit.creator = player_cell;
        let receipt = dregg_turn::TurnReceipt {
            turn_hash: commit.turn_hash,
            forest_hash: [0x66_u8.wrapping_add(ordinal as u8); 32],
            pre_state_hash: actor_root,
            post_state_hash: [0x68_u8.wrapping_add(ordinal as u8); 32],
            timestamp: 1_700_000_000 + i64::try_from(ordinal).expect("test ordinal fits i64"),
            agent: dregg_cell::CellId(player_cell),
            federation_id: world.federation_id(),
            finality: dregg_turn::Finality::Final,
            previous_receipt_hash,
            ..Default::default()
        };
        commit.receipt_hash = receipt.receipt_hash();
        let encoded = postcard::to_stdvec(&receipt).expect("canonical Galley receipt");
        let coordinate = crate::FinalizedTurnCoordinateV2::new(
            world,
            ordinal,
            commit.block_id,
            commit.turn_hash,
            commit.receipt_hash,
            actor_root,
            signer,
        )
        .expect("Galley finalized coordinate");
        (commit, encoded, coordinate, player_cell)
    }

    fn poa_batch_head_count(store: &PersistentStore) -> u64 {
        let read = store.db.begin_read().expect("read transaction");
        read.open_table(crate::poa_event_batch_v2::POA_EVENT_BATCH_HEADS_V2)
            .expect("PoA batch heads")
            .len()
            .expect("PoA batch head count")
    }

    /// The activation executor's signing key. After activation EVERY appended receipt row must be
    /// a canonical `postcard(TurnReceipt)` that is `Final`, carries the activation's federation id,
    /// and is executor-signed by THIS key (`stage_receipt_head_on_append_in`), so tests that commit
    /// past an activation must build their receipts with [`test_activated_receipt`].
    const TEST_ACTIVATION_EXECUTOR_SEED: [u8; 32] = [0xe7; 32];
    /// The federation id `install_test_exact_activation` binds into the activation.
    const TEST_ACTIVATION_FEDERATION_ID: [u8; 32] = [0xe8; 32];

    /// Build the canonical executor-signed receipt row the post-activation receipt authority
    /// demands, and return `(encoded_bytes, receipt_hash)`.
    ///
    /// `previous` is the same agent's prior receipt hash — the per-agent causal chain
    /// `stage_receipt_head_on_append_in` verifies against its derived head index.
    fn test_activated_receipt(
        commit: &CommitRecord,
        previous: Option<[u8; 32]>,
    ) -> (Vec<u8>, [u8; 32]) {
        let key = dregg_types::SigningKey::from_bytes(&TEST_ACTIVATION_EXECUTOR_SEED);
        let mut receipt = dregg_turn::TurnReceipt {
            turn_hash: commit.turn_hash,
            forest_hash: [0xe9; 32],
            pre_state_hash: [0xea; 32],
            post_state_hash: [0xeb; 32],
            timestamp: 1_700_000_000,
            agent: dregg_cell::CellId(commit.creator),
            federation_id: TEST_ACTIVATION_FEDERATION_ID,
            finality: dregg_turn::Finality::Final,
            previous_receipt_hash: previous,
            ..Default::default()
        };
        receipt.executor_signature = Some(
            dregg_types::sign(&key, &receipt.canonical_executor_signed_message())
                .0
                .to_vec(),
        );
        let hash = receipt.receipt_hash();
        (
            postcard::to_stdvec(&receipt).expect("canonical receipt encoding"),
            hash,
        )
    }

    /// Seed shared by the exact-epoch executor AND the faithful hybrid author in
    /// [`commit_test_exact_frame_turn`].
    ///
    /// They cannot be two different keys: `audit_finalized_receipt_cores_v1_on_open`
    /// reauthenticates the durable faithful envelope against the FRAME's executor public key.
    pub(crate) const TEST_EXACT_FRAME_SEED: u8 = 0xe7;

    /// Install the activation [`commit_test_exact_frame_turn`] commits its frames under.
    ///
    /// Its federation is the faithful one, so the frame, the receipt authority and the faithful
    /// note-root edge all name a single federation, as they do in production.
    pub(crate) fn install_test_exact_frame_activation(
        store: &PersistentStore,
    ) -> crate::UntrustedExactFnspV3ActivationV1 {
        let initial = store
            .initialize_exact_fnsp_v3_state_from_faithful_nullifiers()
            .expect("exact prefix from faithful nullifiers");
        let key = dregg_types::SigningKey::from_bytes(&[TEST_EXACT_FRAME_SEED; 32]);
        let public = key.public_key();
        let epoch = dregg_turn::ExactFnspV3ReceiptEpochV1::prepare(
            dregg_turn::ExactFnspV3ReceiptEpoch::new(7).expect("nonzero epoch"),
            faithful_context().1,
            public.0,
            0,
            None,
            dregg_turn::ExactFnspV3StatePoint::new(initial.root(), initial.count())
                .expect("exact point"),
        )
        .expect("activation epoch");
        let signature = dregg_types::sign(
            &key,
            &crate::UntrustedExactFnspV3ActivationV1::signature_message(epoch.activation_hash()),
        );
        let activation = crate::UntrustedExactFnspV3ActivationV1::authenticate_devnet_executor(
            epoch.epoch().get(),
            initial,
            epoch.federation_id(),
            epoch.receipt_cutover_next_index(),
            epoch.receipt_cutover_tail_hash(),
            epoch.activation_hash(),
            public.0,
            signature,
        )
        .expect("signed activation");
        store
            .install_exact_fnsp_v3_activation(activation.clone())
            .expect("install exact frame activation");
        activation
    }

    /// Commit ONE finalized turn carrying an exact FNSP-v3 frame, through the PRODUCTION entry.
    ///
    /// `PersistentStore::open` runs TWO independent boot audits over an exact-frame image, and a
    /// frame satisfies both only as part of a complete finalized turn:
    ///
    /// * `audit_exact_fnsp_v3_faithful_bridge_on_open` requires the faithful nullifier rows and the
    ///   rolling faithful/exact bridge to advance with every exact append;
    /// * `audit_finalized_receipt_cores_v1_on_open` requires a 1:1 FRC1 semantic core that
    ///   REDERIVES at open from the durable commit record, receipt row, faithful note-root envelope
    ///   and attested root.
    ///
    /// No narrower seam produces that image — `stage_exact_fnsp_v3_frame_in` advances the exact
    /// authority and the frame tables alone — so any test that REOPENS its store must build its
    /// frames here.  Tests that never reopen may keep using the narrow seam.
    pub(crate) fn commit_test_exact_frame_turn(
        store: &PersistentStore,
        activation: &crate::UntrustedExactFnspV3ActivationV1,
        ordinal: u64,
        agent: [u8; 32],
        spend: FinalizedNullifierRecord,
        exact_predecessor: Option<&crate::UntrustedExactFnspV3FrameV1>,
        player_predecessor: Option<(u64, [u8; 32])>,
    ) -> crate::UntrustedExactFnspV3FrameV1 {
        let key = dregg_types::SigningKey::from_bytes(&[TEST_EXACT_FRAME_SEED; 32]);
        let signer = FaithfulSigner::new(TEST_EXACT_FRAME_SEED);
        let exact = store
            .prepare_exact_fnsp_v3_append(spend.nullifier, spend.value)
            .expect("exact append candidate");

        let block_id = [0xc0u8.wrapping_add(ordinal as u8); 32];
        let mut commit = faithful_commit_record(ordinal, block_id);
        commit.creator = agent;

        let mut receipt = dregg_turn::TurnReceipt {
            turn_hash: commit.turn_hash,
            forest_hash: [0xe9; 32],
            pre_state_hash: [0xea; 32],
            post_state_hash: [0xeb; 32],
            timestamp: 1_700_000_000,
            agent: dregg_cell::CellId(agent),
            federation_id: activation.federation_id(),
            finality: dregg_turn::Finality::Final,
            previous_receipt_hash: player_predecessor.map(|(_, hash)| hash),
            ..Default::default()
        };
        receipt.executor_signature = Some(
            dregg_types::sign(&key, &receipt.canonical_executor_signed_message())
                .0
                .to_vec(),
        );
        let encoded_receipt = postcard::to_stdvec(&receipt).expect("canonical receipt encoding");
        commit.receipt_hash = receipt.receipt_hash();

        let receipt_index = store.receipt_chain_len().expect("receipt len");
        let frame = crate::exact_fnsp_v3_frame_head::exact_fnsp_v3_test_frame(
            receipt_index,
            activation,
            exact,
            &key,
            &receipt,
            exact_predecessor,
            player_predecessor,
        );

        // `initial_anchor` seeds a FRESH faithful segment and is then compared against the
        // segment's INSTALLED anchor forever after — not against the moving head — so only the
        // first turn may supply it.
        let fresh_segment = store
            .faithful_note_root_head()
            .expect("faithful head")
            .is_none();
        let (anchor, edge) = plan_test_edge(store, commit.height, block_id, &[]);
        let envelope = signer.sign_edge(edge.clone());
        let successor = store
            .plan_faithful_nullifier_successor(std::slice::from_ref(&spend))
            .expect("faithful nullifier successor");
        let attested = test_attested_with_nullifier_root(&signer, &commit, &edge, successor);
        let statements = test_finalized_spend_inputs(store, &anchor, std::slice::from_ref(&spend));
        store
            .commit_finalized_turn_with_faithful_root_and_exact_fnsp_v3_frame(
                ordinal,
                &commit,
                receipt_index,
                &encoded_receipt,
                FinalizedFaithfulRootWeld {
                    initial_anchor: fresh_segment.then_some(&anchor),
                    envelope: &envelope,
                    author_committee: std::slice::from_ref(&signer.ed_pk),
                    author_ml_dsa_committee: std::slice::from_ref(&signer.pq_pk),
                    attested_root: &attested,
                    spent_nullifiers: std::slice::from_ref(&spend),
                    finalized_spends: &statements,
                },
                exact,
                frame.clone(),
                None,
                &crate::FinalizedExecutorConsensusState::default(),
            )
            .expect("production exact-frame finalized turn");
        frame
    }

    fn install_test_exact_activation(
        store: &PersistentStore,
    ) -> crate::UntrustedExactFnspV3ActivationV1 {
        let initial = store
            .initialize_exact_fnsp_v3_state_from_faithful_nullifiers()
            .expect("exact prefix");
        let signing_key = dregg_types::SigningKey::from_bytes(&TEST_ACTIVATION_EXECUTOR_SEED);
        let public_key = signing_key.public_key();
        let epoch = dregg_turn::ExactFnspV3ReceiptEpochV1::prepare(
            dregg_turn::ExactFnspV3ReceiptEpoch::new(7).expect("nonzero epoch"),
            TEST_ACTIVATION_FEDERATION_ID,
            public_key.0,
            0,
            None,
            dregg_turn::ExactFnspV3StatePoint::new(initial.root(), initial.count())
                .expect("exact point"),
        )
        .expect("activation epoch");
        let signature = dregg_types::sign(
            &signing_key,
            &crate::UntrustedExactFnspV3ActivationV1::signature_message(epoch.activation_hash()),
        );
        let activation = crate::UntrustedExactFnspV3ActivationV1::authenticate_devnet_executor(
            epoch.epoch().get(),
            initial,
            epoch.federation_id(),
            epoch.receipt_cutover_next_index(),
            epoch.receipt_cutover_tail_hash(),
            epoch.activation_hash(),
            public_key.0,
            signature,
        )
        .expect("signed activation");
        store
            .install_exact_fnsp_v3_activation(activation.clone())
            .expect("test activation");
        activation
    }

    /// Build a deterministic commit record for ordinal `n`, touching `cells`.
    /// Callers overwrite `turn_hash` / `receipt_hash` to make them unique.
    fn record(n: u64, block_executed_up_to: u64, cells: Vec<Cell>) -> CommitRecord {
        let mut turn_hash = [0u8; 32];
        turn_hash[0] = 0xa0;
        turn_hash[1] = n as u8;
        let mut receipt_hash = [0u8; 32];
        receipt_hash[0] = 0xb0;
        receipt_hash[1] = n as u8;
        CommitRecord {
            ordinal: n, // overwritten by the store with the assigned ordinal
            height: n + 1,
            block_id: [n as u8; 32],
            turn_hash,
            creator: [(n % 3) as u8 + 1; 32],
            receipt_hash,
            ledger_root: [n as u8; 32],
            block_executed_up_to,
            touched_cells: cells,
            removed: Vec::new(),
        }
    }

    #[test]
    fn unpublished_tail_recovery_compares_cursor_receipt_and_publication_head_atomically() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("guarded-tail.redb");
        let store = PersistentStore::open(&path).unwrap();
        let first = record(0, 1, vec![]);
        let second = record(1, 2, vec![]);
        store.commit_finalized_turn(0, &first).unwrap();
        store.commit_finalized_turn(1, &second).unwrap();
        store
            .set_config("test-publication-head", b"published-prefix")
            .unwrap();

        for (cursor, receipt, head) in [
            (3, Some(first.receipt_hash), b"published-prefix".as_slice()),
            (2, Some([0xEE; 32]), b"published-prefix".as_slice()),
            (2, Some(first.receipt_hash), b"stale-prefix".as_slice()),
        ] {
            assert!(
                store
                    .truncate_unpublished_tail(cursor, 1, receipt, "test-publication-head", head)
                    .is_err()
            );
            assert_eq!(store.commit_cursor().unwrap(), 2);
            assert!(store.commit_record_at(1).unwrap().is_some());
        }
        assert_eq!(
            store
                .truncate_unpublished_tail(
                    2,
                    1,
                    Some(first.receipt_hash),
                    "test-publication-head",
                    b"published-prefix"
                )
                .unwrap(),
            1
        );
        drop(store);
        let reopened = PersistentStore::open(&path).unwrap();
        assert_eq!(reopened.commit_cursor().unwrap(), 1);
        assert_eq!(
            reopened.commit_record_at(0).unwrap().unwrap().receipt_hash,
            first.receipt_hash
        );
        assert!(reopened.commit_record_at(1).unwrap().is_none());
        assert_eq!(
            reopened.get_config("test-publication-head").unwrap(),
            Some(b"published-prefix".to_vec())
        );
    }

    fn poa_event(
        store: &PersistentStore,
        record: &CommitRecord,
    ) -> crate::PreparedPoaEventEnvelopeV1 {
        let aggregate = crate::PoaAggregateIdV1::new([0x91; 32], b"galley".to_vec(), [0x92; 32])
            .expect("aggregate");
        let schema = b"galley-v1".to_vec();
        let (sequence, predecessor_digest, semantic_predecessor, genesis) = match store
            .load_poa_event_head(&aggregate, &schema)
            .expect("head")
        {
            Some(head) => (
                head.sequence() + 1,
                head.digest(),
                head.semantic_head(),
                None,
            ),
            None => {
                let projection = br#"{"sequence":0}"#.to_vec();
                let semantic = [0x93; 32];
                let head = crate::PoaEventHeadV1::genesis(
                    aggregate.clone(),
                    schema.clone(),
                    semantic,
                    projection.clone(),
                )
                .expect("genesis");
                (1, head.digest(), semantic, Some(projection))
            }
        };
        crate::PreparedPoaEventEnvelopeV1::new(
            aggregate,
            schema,
            sequence,
            record.ordinal,
            record.turn_hash,
            record.receipt_hash,
            predecessor_digest,
            semantic_predecessor,
            [0xA0_u8.wrapping_add(sequence as u8); 32],
            [0xB0_u8.wrapping_add(sequence as u8); 32],
            vec![sequence as u8],
            vec![sequence as u8, 0xC1],
            genesis,
            0,
        )
        .expect("prepared PoA event")
    }

    fn holding_use(
        record: &CommitRecord,
        event: &crate::PreparedPoaEventEnvelopeV1,
        capability: u8,
        player: u8,
    ) -> crate::PreparedPoaHoldingConsumptionV1 {
        crate::PreparedPoaHoldingConsumptionV1::new_for_legacy_event_test(
            [capability; 32],
            [player; 32],
            [player.wrapping_add(1); 32],
            record,
            event,
            event.stream_digest(),
        )
        .expect("prepared holding consumption")
    }

    fn poa_v2_authority_fixture(
        receipt_signer: [u8; 32],
        coordinate_signer: [u8; 32],
        receipt_actor_root: [u8; 32],
        coordinate_actor_root: [u8; 32],
        receipt_federation: [u8; 32],
        coordinate_federation: [u8; 32],
    ) -> (CommitRecord, Vec<u8>, crate::PreparedPoaEventBatchV2) {
        let mut record = record(0, 0, vec![]);
        record.block_id = [0xA0; 32];
        let receipt = dregg_turn::TurnReceipt {
            turn_hash: record.turn_hash,
            pre_state_hash: receipt_actor_root,
            agent: dregg_cell::CellId::derive_raw(
                &receipt_signer,
                blake3::hash(b"default").as_bytes(),
            ),
            federation_id: receipt_federation,
            finality: dregg_turn::Finality::Final,
            ..Default::default()
        };
        record.receipt_hash = receipt.receipt_hash();
        let encoded = postcard::to_stdvec(&receipt).expect("canonical receipt");
        let world = crate::PoaWorldIdentityV2::new(
            coordinate_federation,
            [0xA1; 32],
            [0xA2; 32],
            [0xA3; 32],
            1,
        )
        .expect("world");
        let coordinate = crate::FinalizedTurnCoordinateV2::new(
            world.clone(),
            record.ordinal,
            record.block_id,
            record.turn_hash,
            record.receipt_hash,
            coordinate_actor_root,
            coordinate_signer,
        )
        .expect("coordinate");
        let stream = crate::PoaBatchStreamIdV2::new(world, 1, [0xA4; 32], 1).expect("stream");
        let semantic_predecessor = [0xA6; 32];
        let genesis_projection = vec![0xAB];
        let predecessor = crate::PoaBatchStreamHeadV2::genesis(
            stream.clone(),
            semantic_predecessor,
            [0xAD; 32],
            genesis_projection.clone(),
        )
        .expect("genesis head");
        let event = crate::PreparedPoaBatchEventV2::new(
            0,
            stream,
            1,
            predecessor.digest(),
            semantic_predecessor,
            [0xA7; 32],
            [0xA8; 32],
            vec![0xA9],
            [0xAE; 32],
            vec![0xAA],
            Some(predecessor.projection_digest()),
            Some(genesis_projection),
        )
        .expect("event");
        let batch = crate::PreparedPoaEventBatchV2::new(
            coordinate,
            b"lean-authoritative-statement".to_vec(),
            [0xAC; 32],
            vec![event],
        )
        .expect("batch");
        (record, encoded, batch)
    }

    /// Rebuild the single-event authority fixture under another exact world while retaining all
    /// finalized receipt coordinates. This is deliberately a *well-shaped* substitution: replay
    /// must reject it because it is not the byte-exact batch durably committed at this ordinal,
    /// not merely because a stream forgot to follow the substituted coordinate.
    fn remap_poa_v2_fixture_world(
        batch: &crate::PreparedPoaEventBatchV2,
        world: crate::PoaWorldIdentityV2,
    ) -> crate::PreparedPoaEventBatchV2 {
        assert_eq!(batch.events().len(), 1, "fixture has one event");
        let coordinate = batch.coordinate();
        let remapped_coordinate = crate::FinalizedTurnCoordinateV2::new(
            world.clone(),
            coordinate.commit_ordinal(),
            coordinate.block_id(),
            coordinate.turn_hash(),
            coordinate.receipt_hash(),
            coordinate.actor_root(),
            coordinate.signer(),
        )
        .expect("remapped coordinate");
        let event = &batch.events()[0];
        let remapped_stream = crate::PoaBatchStreamIdV2::new(
            world,
            event.stream().kind(),
            event.stream().key(),
            event.stream().schema_version(),
        )
        .expect("remapped stream");
        let genesis_projection = event
            .genesis_projection()
            .expect("fixture carries genesis projection")
            .to_vec();
        let genesis_projection_digest = event
            .genesis_projection_digest()
            .expect("fixture carries genesis projection digest");
        let predecessor = crate::PoaBatchStreamHeadV2::genesis(
            remapped_stream.clone(),
            event.semantic_predecessor(),
            genesis_projection_digest,
            genesis_projection.clone(),
        )
        .expect("remapped genesis head");
        let remapped_event = crate::PreparedPoaBatchEventV2::new(
            event.event_index(),
            remapped_stream,
            event.sequence(),
            predecessor.digest(),
            event.semantic_predecessor(),
            event.event_digest(),
            event.payload_digest(),
            event.payload().to_vec(),
            event.successor_projection_digest(),
            event.successor_projection().to_vec(),
            Some(genesis_projection_digest),
            Some(genesis_projection),
        )
        .expect("remapped event");
        crate::PreparedPoaEventBatchV2::new(
            remapped_coordinate,
            b"lean-authoritative-statement".to_vec(),
            batch.batch_digest(),
            vec![remapped_event],
        )
        .expect("remapped batch")
    }

    fn exact_poa_v2_holding(
        batch: &crate::PreparedPoaEventBatchV2,
        player: [u8; 32],
        player_cell: [u8; 32],
    ) -> crate::PreparedPoaHoldingConsumptionV1 {
        crate::PreparedPoaHoldingConsumptionV1::new(
            [0xAD; 32],
            [0xAE; 32],
            player,
            player_cell,
            [0xAF; 32],
            [0xB0; 32],
            batch,
            0,
        )
        .expect("holding")
    }

    fn install_active_poa_world(store: &PersistentStore, world: crate::PoaWorldIdentityV2) -> bool {
        // ⚑ ARMED (2026-08-08). `false` here means EXACTLY "the archive lacks the export" — every
        // other path below `expect`s — so three callers that read it as
        // `if !install_active_poa_world(..) { return; }` (`:5800`, `:5968`, `:6161`) were silent
        // skips. `:6161` is `poa_v2_central_writer_refuses_absent_or_wrong_active_world`, where the
        // skipped half is the "WRONG active world" leg — the one the test is named for.
        if !dregg_lean_ffi::demand_lean(
            dregg_lean_ffi::poa_world_activation_ffi::poa_world_activation_available(),
            "installing an active PoA world (dregg_poa_world_activation_*)",
        ) {
            return false;
        }
        let curator = ed25519_dalek::SigningKey::from_bytes(&[0xC7; 32]);
        let statement = crate::PoaWorldActivationStatementV1::new(
            world,
            1,
            [0; 32],
            crate::PoaWorldActivationKindV1::Advance,
            None,
        )
        .expect("bootstrap world statement");
        let signature = curator
            .sign(&statement.signing_message().expect("world signing message"))
            .to_bytes();
        let envelope = crate::SignedPoaWorldActivationEnvelopeV1::new(
            statement,
            curator.verifying_key().to_bytes(),
            signature,
        )
        .expect("signed bootstrap world");
        store
            .install_poa_world_curator_pin_v1(curator.verifying_key().to_bytes())
            .expect("curator pin");
        store
            .install_poa_world_activation_v1(envelope)
            .expect("native-Lean-authorized active world");
        true
    }

    fn advance_active_poa_world(store: &PersistentStore, world: crate::PoaWorldIdentityV2) {
        let predecessor = store
            .load_poa_active_world_v1()
            .expect("active-world load")
            .expect("active-world head");
        let curator = ed25519_dalek::SigningKey::from_bytes(&[0xC7; 32]);
        let statement = crate::PoaWorldActivationStatementV1::new(
            world,
            predecessor.counter() + 1,
            predecessor.prepared().record().envelope_digest(),
            crate::PoaWorldActivationKindV1::Advance,
            None,
        )
        .expect("successor world statement");
        let signature = curator
            .sign(&statement.signing_message().expect("world signing message"))
            .to_bytes();
        let envelope = crate::SignedPoaWorldActivationEnvelopeV1::new(
            statement,
            curator.verifying_key().to_bytes(),
            signature,
        )
        .expect("signed successor world");
        store
            .install_poa_world_activation_v1(envelope)
            .expect("native-Lean-authorized successor world");
    }

    #[test]
    fn poa_galley_commit_adapter_commits_replays_historical_world_and_refuses_omission() {
        if !galley_native_available() {
            return;
        }
        let store = PersistentStore::open_in_memory().expect("store");
        let world_v1 = galley_world(0x51);
        assert!(install_active_poa_world(&store, world_v1.clone()));
        let policy = galley_policy(world_v1.clone());
        let (record, receipt, coordinate, player_cell) =
            galley_turn_material(world_v1.clone(), 0, None);
        let sealed = store
            .prepare_poa_galley_public_event_batch_for_commit_test(&policy, coordinate, player_cell)
            .expect("sealed Galley batch");
        let exact_retry = sealed.clone();
        let faithful = galley_faithful_fixture(&store, &record, None);
        let executor = crate::FinalizedExecutorConsensusState::default();

        let fresh = store
            .commit_finalized_turn_with_faithful_root_and_executor_state_and_poa_galley(
                0,
                &record,
                &[],
                0,
                &receipt,
                faithful.weld(),
                &executor,
                sealed,
            )
            .expect("fresh Galley commit");
        assert!(fresh.freshly_committed);
        assert_eq!(store.commit_cursor().unwrap(), 1);
        assert_eq!(store.receipt_chain_len().unwrap(), 1);
        assert!(store.load_poa_event_batch_v2(0).unwrap().is_some());
        assert_eq!(poa_batch_head_count(&store), 1);

        let world_v2 = crate::PoaWorldIdentityV2::new(
            world_v1.federation_id(),
            [0x59; 32],
            [0x5a; 32],
            [0x5b; 32],
            world_v1.content_epoch() + 1,
        )
        .expect("successor Galley world");
        advance_active_poa_world(&store, world_v2);
        let replay = store
            .commit_finalized_turn_with_faithful_root_and_executor_state_and_poa_galley(
                0,
                &record,
                &[],
                0,
                &receipt,
                faithful.weld(),
                &executor,
                exact_retry,
            )
            .expect("exact W1 retry after W2 rotation");
        assert!(!replay.freshly_committed);

        let omitted = store
            .commit_finalized_turn_with_faithful_root_and_executor_state(
                0,
                &record,
                &[],
                0,
                &receipt,
                faithful.weld(),
                &executor,
            )
            .expect_err("a replay cannot omit its Galley batch");
        assert!(omitted.to_string().contains("omitted its PoA V2 batch"));
    }

    #[test]
    fn poa_galley_commit_adapter_wrong_current_world_rolls_back_every_weld() {
        if !galley_native_available() {
            return;
        }
        let store = PersistentStore::open_in_memory().expect("store");
        let world_v1 = galley_world(0x52);
        assert!(install_active_poa_world(&store, world_v1.clone()));
        let policy = galley_policy(world_v1.clone());
        let (record, receipt, coordinate, player_cell) =
            galley_turn_material(world_v1.clone(), 0, None);
        let sealed = store
            .prepare_poa_galley_public_event_batch_for_commit_test(&policy, coordinate, player_cell)
            .expect("sealed Galley batch");

        let world_v2 = crate::PoaWorldIdentityV2::new(
            world_v1.federation_id(),
            [0x5c; 32],
            [0x5d; 32],
            [0x5e; 32],
            world_v1.content_epoch() + 1,
        )
        .expect("successor Galley world");
        advance_active_poa_world(&store, world_v2);

        let faithful = galley_faithful_fixture(&store, &record, Some(0xe1));
        let executor = crate::FinalizedExecutorConsensusState::default();
        let error = store
            .commit_finalized_turn_with_faithful_root_and_executor_state_and_poa_galley(
                0,
                &record,
                &[],
                0,
                &receipt,
                faithful.weld(),
                &executor,
                sealed,
            )
            .expect_err("stale world must abort the sole writer");
        assert!(error.to_string().contains("active world"));
        assert_eq!(store.commit_cursor().unwrap(), 0);
        assert!(store.commit_record_at(0).unwrap().is_none());
        assert_eq!(store.receipt_chain_len().unwrap(), 0);
        assert!(store.load_poa_event_batch_v2(0).unwrap().is_none());
        assert_eq!(poa_batch_head_count(&store), 0);
        assert!(store.load_faithful_nullifier_records().unwrap().is_empty());
        assert!(store.faithful_note_root_head().unwrap().is_none());
    }

    #[test]
    fn poa_galley_commit_adapter_concurrent_stale_stream_head_rolls_back_later_turn() {
        if !galley_native_available() {
            return;
        }
        let store = PersistentStore::open_in_memory().expect("store");
        let world = galley_world(0x53);
        assert!(install_active_poa_world(&store, world.clone()));
        let policy = galley_policy(world.clone());
        let (record0, receipt0, coordinate0, player_cell0) =
            galley_turn_material(world.clone(), 0, None);
        let (record1, receipt1, coordinate1, player_cell1) =
            galley_turn_material(world, 1, Some(record0.receipt_hash));

        // Both candidates are prepared from sequence zero. Only one may win
        // the durable stream-head CAS.
        let batch0 = store
            .prepare_poa_galley_public_event_batch_for_commit_test(
                &policy,
                coordinate0,
                player_cell0,
            )
            .expect("first Galley batch");
        let stale_batch1 = store
            .prepare_poa_galley_public_event_batch_for_commit_test(
                &policy,
                coordinate1,
                player_cell1,
            )
            .expect("concurrent Galley batch");
        let faithful0 = galley_faithful_fixture(&store, &record0, None);
        let executor0 = crate::FinalizedExecutorConsensusState::default();
        store
            .commit_finalized_turn_with_faithful_root_and_executor_state_and_poa_galley(
                0,
                &record0,
                &[],
                0,
                &receipt0,
                faithful0.weld(),
                &executor0,
                batch0,
            )
            .expect("first Galley commit");

        let faithful1 = galley_faithful_fixture(&store, &record1, Some(0xe2));
        let executor1 = crate::FinalizedExecutorConsensusState::default();
        store
            .commit_finalized_turn_with_faithful_root_and_executor_state_and_poa_galley(
                1,
                &record1,
                &[],
                1,
                &receipt1,
                faithful1.weld(),
                &executor1,
                stale_batch1,
            )
            .expect_err("concurrent stale stream head must abort");

        assert_eq!(store.commit_cursor().unwrap(), 1);
        assert!(store.commit_record_at(1).unwrap().is_none());
        assert_eq!(store.receipt_chain_len().unwrap(), 1);
        assert!(store.load_poa_event_batch_v2(1).unwrap().is_none());
        assert_eq!(poa_batch_head_count(&store), 1);
        assert!(store.load_faithful_nullifier_records().unwrap().is_empty());
    }

    #[test]
    fn poa_galley_commit_adapter_refuses_invented_batch_on_exact_turn_replay() {
        if !galley_native_available() {
            return;
        }
        let store = PersistentStore::open_in_memory().expect("store");
        let world = galley_world(0x54);
        assert!(install_active_poa_world(&store, world.clone()));
        let policy = galley_policy(world.clone());
        let (record, receipt, coordinate, player_cell) = galley_turn_material(world, 0, None);
        let invented = store
            .prepare_poa_galley_public_event_batch_for_commit_test(&policy, coordinate, player_cell)
            .expect("candidate Galley batch");
        let faithful = galley_faithful_fixture(&store, &record, None);
        let executor = crate::FinalizedExecutorConsensusState::default();

        store
            .commit_finalized_turn_with_faithful_root_and_executor_state(
                0,
                &record,
                &[],
                0,
                &receipt,
                faithful.weld(),
                &executor,
            )
            .expect("generic finalized turn without Galley");
        let error = store
            .commit_finalized_turn_with_faithful_root_and_executor_state_and_poa_galley(
                0,
                &record,
                &[],
                0,
                &receipt,
                faithful.weld(),
                &executor,
                invented,
            )
            .expect_err("an exact retry cannot invent a Galley batch");
        assert!(error.to_string().contains("invented a PoA V2 batch"));
        assert_eq!(store.commit_cursor().unwrap(), 1);
        assert_eq!(store.receipt_chain_len().unwrap(), 1);
        assert!(store.load_poa_event_batch_v2(0).unwrap().is_none());
        assert_eq!(poa_batch_head_count(&store), 0);
    }

    #[test]
    fn poa_galley_raw_apex_commits_and_replays_stored_w1_bytes_after_w2_rotation() {
        if !galley_native_available() {
            return;
        }
        let store = PersistentStore::open_in_memory().expect("store");
        let (world_v1, manifest_v1) = raw_galley_world_bundle(0x51, 0x52, 1, 19);
        install_raw_galley_world_and_content(&store, world_v1.clone(), manifest_v1);
        let policy_v1 = store
            .load_authenticated_poa_galley_policy_v1()
            .expect("authenticated W1 policy");
        let action_token = store
            .offered_poa_galley_public_token_for_commit_test(
                &policy_v1,
                raw_galley_signer(),
                raw_galley_player_cell(),
            )
            .expect("native W1 action token");
        let (signed, receipt, record) =
            raw_galley_turn_material(&world_v1, 0, None, action_token, [19; 32]);
        let faithful = galley_faithful_fixture(&store, &record, None);
        let executor = crate::FinalizedExecutorConsensusState::default();

        let fresh = store
            .commit_finalized_poa_galley_public_perform_v1(
                0,
                &record,
                &[],
                0,
                &signed,
                &receipt,
                faithful.weld(),
                &executor,
            )
            .expect("fresh raw Galley commit");
        assert!(fresh.freshly_committed);
        let stored_before_rotation = store
            .load_poa_event_batch_v2(0)
            .expect("batch load")
            .expect("stored raw Galley batch");

        let (world_v2, _) = raw_galley_world_bundle(0x53, 0x54, 2, 29);
        advance_active_poa_world(&store, world_v2);
        let replay = store
            .commit_finalized_poa_galley_public_perform_v1(
                0,
                &record,
                &[],
                0,
                &signed,
                &receipt,
                faithful.weld(),
                &executor,
            )
            .expect("historical raw W1 replay after W2 rotation");
        assert!(!replay.freshly_committed);
        assert_eq!(
            store.load_poa_event_batch_v2(0).unwrap().unwrap(),
            stored_before_rotation,
            "retry retains the historical signed-world batch exactly",
        );
        assert_eq!(store.commit_cursor().unwrap(), 1);
        assert_eq!(store.receipt_chain_len().unwrap(), 1);
        assert_eq!(poa_batch_head_count(&store), 1);
    }

    #[test]
    fn poa_galley_raw_apex_rejects_stale_world_carrier_and_rolls_back_every_weld() {
        if !galley_native_available() {
            return;
        }
        let store = PersistentStore::open_in_memory().expect("store");
        let (world_v1, manifest_v1) = raw_galley_world_bundle(0x61, 0x62, 1, 19);
        install_raw_galley_world_and_content(&store, world_v1.clone(), manifest_v1);
        let policy_v1 = store
            .load_authenticated_poa_galley_policy_v1()
            .expect("authenticated W1 policy");
        let token_v1 = store
            .offered_poa_galley_public_token_for_commit_test(
                &policy_v1,
                raw_galley_signer(),
                raw_galley_player_cell(),
            )
            .expect("native W1 token");
        let (signed_v1, receipt_v1, record) =
            raw_galley_turn_material(&world_v1, 0, None, token_v1, [19; 32]);

        // The successor world authenticates a different public action member.
        // The stale SignedTurn carries no caller-selected world for persistence
        // to trust; the one-writer apex must derive W2 and reject the W1 action.
        let (world_v2, manifest_v2) = raw_galley_world_bundle(0x63, 0x64, 2, 29);
        advance_raw_galley_world_and_content(&store, world_v2, manifest_v2);
        let faithful = galley_faithful_fixture(&store, &record, Some(0xe3));
        let executor = crate::FinalizedExecutorConsensusState::default();
        store
            .commit_finalized_poa_galley_public_perform_v1(
                0,
                &record,
                &[],
                0,
                &signed_v1,
                &receipt_v1,
                faithful.weld(),
                &executor,
            )
            .expect_err("stale W1 carrier must not authorize a W2 event");

        assert_eq!(store.commit_cursor().unwrap(), 0);
        assert!(store.commit_record_at(0).unwrap().is_none());
        assert_eq!(store.receipt_chain_len().unwrap(), 0);
        assert!(store.load_poa_event_batch_v2(0).unwrap().is_none());
        assert_eq!(poa_batch_head_count(&store), 0);
        assert!(store.load_faithful_nullifier_records().unwrap().is_empty());
        assert!(store.faithful_note_root_head().unwrap().is_none());
    }

    #[test]
    fn poa_galley_raw_apex_rejects_invalid_signature_after_staging_and_rolls_back() {
        if !galley_native_available() {
            return;
        }
        let store = PersistentStore::open_in_memory().expect("store");
        let (world, manifest) = raw_galley_world_bundle(0x71, 0x72, 1, 19);
        install_raw_galley_world_and_content(&store, world.clone(), manifest);
        let policy = store
            .load_authenticated_poa_galley_policy_v1()
            .expect("authenticated policy");
        let token = store
            .offered_poa_galley_public_token_for_commit_test(
                &policy,
                raw_galley_signer(),
                raw_galley_player_cell(),
            )
            .expect("native action token");
        let (mut signed, receipt, record) =
            raw_galley_turn_material(&world, 0, None, token, [19; 32]);
        signed.signature = dregg_types::Signature([0; 64]);
        let faithful = galley_faithful_fixture(&store, &record, Some(0xe4));
        let executor = crate::FinalizedExecutorConsensusState::default();
        store
            .commit_finalized_poa_galley_public_perform_v1(
                0,
                &record,
                &[],
                0,
                &signed,
                &receipt,
                faithful.weld(),
                &executor,
            )
            .expect_err("forged raw SignedTurn must fail inside the commit writer");

        assert_eq!(store.commit_cursor().unwrap(), 0);
        assert_eq!(store.receipt_chain_len().unwrap(), 0);
        assert!(store.load_poa_event_batch_v2(0).unwrap().is_none());
        assert_eq!(poa_batch_head_count(&store), 0);
        assert!(store.load_faithful_nullifier_records().unwrap().is_empty());
        assert!(store.faithful_note_root_head().unwrap().is_none());
    }

    #[test]
    fn poa_galley_raw_apex_refuses_replay_invention_and_extends_heads_in_writer() {
        if !galley_native_available() {
            return;
        }

        // First, a generic finalized turn cannot acquire Galley history later
        // merely because its retry presents a valid signed Galley carrier.
        let generic = PersistentStore::open_in_memory().expect("generic store");
        let (generic_world, generic_manifest) = raw_galley_world_bundle(0x81, 0x82, 1, 19);
        install_raw_galley_world_and_content(&generic, generic_world.clone(), generic_manifest);
        let generic_policy = generic
            .load_authenticated_poa_galley_policy_v1()
            .expect("generic policy");
        let generic_token = generic
            .offered_poa_galley_public_token_for_commit_test(
                &generic_policy,
                raw_galley_signer(),
                raw_galley_player_cell(),
            )
            .expect("generic token");
        let (generic_signed, generic_receipt, generic_record) =
            raw_galley_turn_material(&generic_world, 0, None, generic_token, [19; 32]);
        let generic_receipt_bytes =
            postcard::to_stdvec(&generic_receipt).expect("canonical receipt");
        let generic_faithful = galley_faithful_fixture(&generic, &generic_record, None);
        let executor = crate::FinalizedExecutorConsensusState::default();
        generic
            .commit_finalized_turn_with_faithful_root_and_executor_state(
                0,
                &generic_record,
                &[],
                0,
                &generic_receipt_bytes,
                generic_faithful.weld(),
                &executor,
            )
            .expect("generic finalized commit");
        let invention = generic
            .commit_finalized_poa_galley_public_perform_v1(
                0,
                &generic_record,
                &[],
                0,
                &generic_signed,
                &generic_receipt,
                generic_faithful.weld(),
                &executor,
            )
            .expect_err("raw retry cannot invent Galley history");
        assert!(invention.to_string().contains("invented a batch"));
        assert!(generic.load_poa_event_batch_v2(0).unwrap().is_none());

        // Then prove that fresh raw turns do not expose a caller-side planning
        // gap: each transaction reads the latest stream head and plans the next
        // event under that same writer snapshot.
        let store = PersistentStore::open_in_memory().expect("extension store");
        let (world, manifest) = raw_galley_world_bundle(0x83, 0x84, 1, 19);
        install_raw_galley_world_and_content(&store, world.clone(), manifest);
        let policy = store
            .load_authenticated_poa_galley_policy_v1()
            .expect("extension policy");
        let token0 = store
            .offered_poa_galley_public_token_for_commit_test(
                &policy,
                raw_galley_signer(),
                raw_galley_player_cell(),
            )
            .expect("sequence-zero token");
        let (signed0, receipt0, record0) =
            raw_galley_turn_material(&world, 0, None, token0, [19; 32]);
        let faithful0 = galley_faithful_fixture(&store, &record0, None);
        store
            .commit_finalized_poa_galley_public_perform_v1(
                0,
                &record0,
                &[],
                0,
                &signed0,
                &receipt0,
                faithful0.weld(),
                &executor,
            )
            .expect("first in-writer plan");

        let policy = store
            .load_authenticated_poa_galley_policy_v1()
            .expect("same active policy");
        let token1 = store
            .offered_poa_galley_public_token_for_commit_test(
                &policy,
                raw_galley_signer_for(0x42),
                raw_galley_player_cell_for(0x42),
            )
            .expect("sequence-one token");
        let (signed1, receipt1, record1) =
            raw_galley_turn_material_for(&world, 1, None, token1, [19; 32], 0x42);
        let faithful1 = galley_faithful_fixture(&store, &record1, None);
        store
            .commit_finalized_poa_galley_public_perform_v1(
                1,
                &record1,
                &[],
                1,
                &signed1,
                &receipt1,
                faithful1.weld(),
                &executor,
            )
            .expect("second in-writer plan extends current head");

        let second = store
            .load_poa_event_batch_v2(1)
            .expect("second batch load")
            .expect("second batch");
        assert_eq!(second.events().len(), 1);
        assert_eq!(second.events()[0].sequence(), 2);
        assert_eq!(store.commit_cursor().unwrap(), 2);
        assert_eq!(store.receipt_chain_len().unwrap(), 2);
        assert_eq!(poa_batch_head_count(&store), 1);
    }

    #[test]
    fn poa_v2_authority_weld_refuses_coordinate_and_receipt_substitution() {
        let signer = [0xB1; 32];
        let actor_root = [0xB2; 32];
        let federation = [0xB3; 32];
        let (record, encoded, batch) = poa_v2_authority_fixture(
            signer, signer, actor_root, actor_root, federation, federation,
        );
        validate_poa_v2_batch_authority(&record, &encoded, &batch, None).unwrap();

        let (_, _, altered_actor) = poa_v2_authority_fixture(
            signer, signer, actor_root, [0xC1; 32], federation, federation,
        );
        assert!(validate_poa_v2_batch_authority(&record, &encoded, &altered_actor, None).is_err());
        let (_, _, altered_signer) = poa_v2_authority_fixture(
            signer, [0xC2; 32], actor_root, actor_root, federation, federation,
        );
        assert!(validate_poa_v2_batch_authority(&record, &encoded, &altered_signer, None).is_err());
        let (_, _, altered_federation) = poa_v2_authority_fixture(
            signer, signer, actor_root, actor_root, federation, [0xC3; 32],
        );
        assert!(
            validate_poa_v2_batch_authority(&record, &encoded, &altered_federation, None).is_err()
        );

        let mut noncanonical = encoded.clone();
        noncanonical.push(0);
        assert!(validate_poa_v2_batch_authority(&record, &noncanonical, &batch, None).is_err());
    }

    #[test]
    fn poa_v2_authority_weld_refuses_holding_player_or_cell_substitution() {
        let signer = [0xD1; 32];
        let actor_root = [0xD2; 32];
        let federation = [0xD3; 32];
        let (record, encoded, batch) = poa_v2_authority_fixture(
            signer, signer, actor_root, actor_root, federation, federation,
        );
        let player_cell =
            dregg_cell::CellId::derive_raw(&signer, blake3::hash(b"default").as_bytes()).0;
        let exact = exact_poa_v2_holding(&batch, signer, player_cell);
        validate_poa_v2_batch_authority(&record, &encoded, &batch, Some(&exact)).unwrap();
        assert!(exact.matches_poa_batch(&batch));

        let altered_player = exact_poa_v2_holding(&batch, [0xD4; 32], player_cell);
        assert!(
            validate_poa_v2_batch_authority(&record, &encoded, &batch, Some(&altered_player),)
                .is_err()
        );
        assert!(!altered_player.matches_poa_batch(&batch));

        let altered_cell = exact_poa_v2_holding(&batch, signer, [0xD5; 32]);
        assert!(
            validate_poa_v2_batch_authority(&record, &encoded, &batch, Some(&altered_cell),)
                .is_err()
        );
        assert!(!altered_cell.matches_poa_batch(&batch));
    }

    #[test]
    fn poa_v2_central_writer_commits_and_replays_exact_batch_and_holding() {
        let store = PersistentStore::open_in_memory().unwrap();
        let signer = [0xE1; 32];
        let actor_root = [0xE2; 32];
        let federation = [0xE3; 32];
        let (record, encoded, batch) = poa_v2_authority_fixture(
            signer, signer, actor_root, actor_root, federation, federation,
        );
        if !install_active_poa_world(&store, batch.coordinate().world().clone()) {
            return;
        }
        let player_cell =
            dregg_cell::CellId::derive_raw(&signer, blake3::hash(b"default").as_bytes()).0;
        let holding = exact_poa_v2_holding(&batch, signer, player_cell);

        let commit = || {
            store.commit_finalized_turn_welded(
                0,
                &record,
                &[],
                &[],
                Some(ReceiptWeldMode::AppendOrVerify {
                    index: 0,
                    encoded: &encoded,
                }),
                None,
                None,
                None,
                &[],
                None,
                None,
                Some(&batch),
                Some(&holding),
            )
        };
        assert!(commit().unwrap().outcome.freshly_committed);
        assert!(!commit().unwrap().outcome.freshly_committed);
        assert_eq!(
            store.load_poa_event_batch_v2(0).unwrap(),
            Some(batch.clone())
        );
        let stored_holding = store
            .load_poa_holding_consumption(&holding.capability_receipt_id())
            .unwrap()
            .unwrap();
        assert_eq!(stored_holding.turn_hash(), record.turn_hash);
        assert_eq!(stored_holding.holder_wallet(), [0xAE; 32]);
        assert_eq!(stored_holding.action_token(), [0xAF; 32]);
        assert_eq!(stored_holding.beneficiary_player_id(), [0xB0; 32]);

        let redirected_intent = crate::PreparedPoaHoldingConsumptionV1::new(
            holding.capability_receipt_id(),
            holding.holder_wallet(),
            signer,
            player_cell,
            [0xC1; 32],
            [0xC2; 32],
            &batch,
            0,
        )
        .expect("redirected intent");
        let redirected_error = match store.commit_finalized_turn_welded(
            0,
            &record,
            &[],
            &[],
            Some(ReceiptWeldMode::AppendOrVerify {
                index: 0,
                encoded: &encoded,
            }),
            None,
            None,
            None,
            &[],
            None,
            None,
            Some(&batch),
            Some(&redirected_intent),
        ) {
            Err(error) => error,
            Ok(_) => panic!("replay may not redirect action or beneficiary"),
        };
        assert!(redirected_error.to_string().contains("byte-identical"));
        assert!(
            store.commit_finalized_turn(0, &record).is_err(),
            "replay may not omit its receipt, V2 batch, or holding weld"
        );
        store.audit_poa_event_batch_store_v2().unwrap();
        store.audit_poa_holding_consumptions().unwrap();

        let committed_world = batch.coordinate().world();
        let successor_world = crate::PoaWorldIdentityV2::new(
            committed_world.federation_id(),
            [0xF2; 32],
            [0xF3; 32],
            [0xF4; 32],
            committed_world.content_epoch() + 1,
        )
        .unwrap();
        advance_active_poa_world(&store, successor_world.clone());
        assert!(
            !commit().unwrap().outcome.freshly_committed,
            "a current node must rebuild an exact W1 batch after legitimate activation of W2"
        );

        let substituted_w2 = remap_poa_v2_fixture_world(&batch, successor_world);
        let substituted_w2_holding = exact_poa_v2_holding(&substituted_w2, signer, player_cell);
        assert!(
            store
                .commit_finalized_turn_welded(
                    0,
                    &record,
                    &[],
                    &[],
                    Some(ReceiptWeldMode::AppendOrVerify {
                        index: 0,
                        encoded: &encoded,
                    }),
                    None,
                    None,
                    None,
                    &[],
                    None,
                    None,
                    Some(&substituted_w2),
                    Some(&substituted_w2_holding),
                )
                .is_err(),
            "an authenticated W2 coordinate cannot replace the byte-exact W1 replay"
        );

        let forged_w0 =
            crate::PoaWorldIdentityV2::new(federation, [0xD2; 32], [0xD3; 32], [0xD4; 32], 1)
                .unwrap();
        let substituted_w0 = remap_poa_v2_fixture_world(&batch, forged_w0);
        let substituted_w0_holding = exact_poa_v2_holding(&substituted_w0, signer, player_cell);
        assert!(
            store
                .commit_finalized_turn_welded(
                    0,
                    &record,
                    &[],
                    &[],
                    Some(ReceiptWeldMode::AppendOrVerify {
                        index: 0,
                        encoded: &encoded,
                    }),
                    None,
                    None,
                    None,
                    &[],
                    None,
                    None,
                    Some(&substituted_w0),
                    Some(&substituted_w0_holding),
                )
                .is_err(),
            "a well-shaped but never-activated world cannot replay a finalized W1 batch"
        );
    }

    #[test]
    fn poa_v2_and_holding_compaction_reopen_keep_exact_retry_and_coordinates() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("poa-v2-holding-compacted.redb");
        let signer = [0x91; 32];
        let actor_root = [0x92; 32];
        let federation = [0x93; 32];
        let (fixture_record, encoded, batch) = poa_v2_authority_fixture(
            signer, signer, actor_root, actor_root, federation, federation,
        );
        let player_cell =
            dregg_cell::CellId::derive_raw(&signer, blake3::hash(b"default").as_bytes()).0;
        let holding = exact_poa_v2_holding(&batch, signer, player_cell);
        {
            let store = PersistentStore::open(&path).unwrap();
            if !install_active_poa_world(&store, batch.coordinate().world().clone()) {
                return;
            }
            store
                .commit_finalized_turn_welded(
                    0,
                    &fixture_record,
                    &[],
                    &[],
                    Some(ReceiptWeldMode::AppendOrVerify {
                        index: 0,
                        encoded: &encoded,
                    }),
                    None,
                    None,
                    None,
                    &[],
                    None,
                    None,
                    Some(&batch),
                    Some(&holding),
                )
                .unwrap();
            let mut survivor = record(1, 1, Vec::new());
            survivor.ledger_root = fixture_record.ledger_root;
            store.commit_finalized_turn(1, &survivor).unwrap();
            store
                .store_ledger_checkpoint_snapshot(&crate::LedgerCheckpoint {
                    height: 2,
                    cells: Vec::new(),
                    sovereign_commitments: Vec::new(),
                    sovereign_registrations: Vec::new(),
                })
                .unwrap();
            assert_eq!(store.compact_below_with_test_poa_anchor_v1(2).unwrap(), 1);
            assert!(store.commit_record_at(0).unwrap().is_none());
            store.audit_poa_event_batch_store_v2().unwrap();
            store.audit_poa_holding_consumptions().unwrap();
        }

        let reopened = PersistentStore::open_with_test_poa_compact_trust_v1(&path).unwrap();
        assert_eq!(
            reopened.load_poa_event_batch_v2(0).unwrap(),
            Some(batch.clone())
        );
        assert!(
            !reopened
                .commit_finalized_turn_welded(
                    0,
                    &fixture_record,
                    &[],
                    &[],
                    Some(ReceiptWeldMode::AppendOrVerify {
                        index: 0,
                        encoded: &encoded,
                    }),
                    None,
                    None,
                    None,
                    &[],
                    None,
                    None,
                    Some(&batch),
                    Some(&holding),
                )
                .unwrap()
                .outcome
                .freshly_committed,
            "byte-exact V2 plus holding retry must survive compaction and reopen"
        );

        let mut substituted_record = fixture_record.clone();
        substituted_record.creator[0] ^= 1;
        assert!(
            reopened
                .commit_finalized_turn_welded(
                    0,
                    &substituted_record,
                    &[],
                    &[],
                    Some(ReceiptWeldMode::AppendOrVerify {
                        index: 0,
                        encoded: &encoded,
                    }),
                    None,
                    None,
                    None,
                    &[],
                    None,
                    None,
                    Some(&batch),
                    Some(&holding),
                )
                .is_err(),
            "compacted V2 replay may not substitute the generic authority tuple"
        );
        assert!(
            reopened
                .commit_finalized_turn_welded(
                    0,
                    &fixture_record,
                    &[],
                    &[],
                    Some(ReceiptWeldMode::AppendOrVerify {
                        index: 0,
                        encoded: &encoded,
                    }),
                    None,
                    None,
                    None,
                    &[],
                    None,
                    None,
                    Some(&batch),
                    None,
                )
                .is_err(),
            "compacted V2 replay may not omit the certified holding sidecar"
        );

        let (_, _, substituted_batch) = poa_v2_authority_fixture(
            signer, signer, actor_root, [0x94; 32], federation, federation,
        );
        let substituted_holding = exact_poa_v2_holding(&substituted_batch, signer, player_cell);
        assert!(
            reopened
                .commit_finalized_turn_welded(
                    0,
                    &fixture_record,
                    &[],
                    &[],
                    Some(ReceiptWeldMode::AppendOrVerify {
                        index: 0,
                        encoded: &encoded,
                    }),
                    None,
                    None,
                    None,
                    &[],
                    None,
                    None,
                    Some(&substituted_batch),
                    Some(&substituted_holding),
                )
                .is_err(),
            "a compacted manifest cannot substitute its finalized actor-root coordinate"
        );
    }

    #[test]
    fn poa_v2_central_writer_refuses_absent_or_wrong_active_world() {
        let signer = [0xE4; 32];
        let actor_root = [0xE5; 32];
        let federation = [0xE6; 32];
        let (record, encoded, batch) = poa_v2_authority_fixture(
            signer, signer, actor_root, actor_root, federation, federation,
        );
        let commit = |store: &PersistentStore| {
            store.commit_finalized_turn_welded(
                0,
                &record,
                &[],
                &[],
                Some(ReceiptWeldMode::AppendOrVerify {
                    index: 0,
                    encoded: &encoded,
                }),
                None,
                None,
                None,
                &[],
                None,
                None,
                Some(&batch),
                None,
            )
        };

        let absent = PersistentStore::open_in_memory().unwrap();
        assert!(commit(&absent).is_err());
        assert_eq!(absent.commit_cursor().unwrap(), 0);
        assert!(absent.load_poa_event_batch_v2(0).unwrap().is_none());

        let wrong = PersistentStore::open_in_memory().unwrap();
        let expected = batch.coordinate().world();
        let wrong_world = crate::PoaWorldIdentityV2::new(
            expected.federation_id(),
            [0xF1; 32],
            expected.activation_digest(),
            expected.content_session(),
            expected.content_epoch(),
        )
        .unwrap();
        if !install_active_poa_world(&wrong, wrong_world) {
            return;
        }
        assert!(commit(&wrong).is_err());
        assert_eq!(wrong.commit_cursor().unwrap(), 0);
        assert!(wrong.load_poa_event_batch_v2(0).unwrap().is_none());
    }

    #[test]
    fn poa_holding_consumption_replay_is_exact_and_one_shot() {
        let store = PersistentStore::open_in_memory().unwrap();
        let first = record(0, 0, vec![]);
        let first_event = poa_event(&store, &first);
        let use_a = holding_use(&first, &first_event, 0x71, 0x31);

        let fresh = store
            .commit_finalized_turn_welded(
                0,
                &first,
                &[],
                &[],
                None,
                None,
                None,
                None,
                &[],
                None,
                Some(&first_event),
                None,
                Some(&use_a),
            )
            .unwrap();
        assert!(fresh.outcome.freshly_committed);
        assert_eq!(
            store
                .load_poa_holding_consumption(&[0x71; 32])
                .unwrap()
                .unwrap()
                .turn_hash(),
            first.turn_hash
        );

        let replay = store
            .commit_finalized_turn_welded(
                0,
                &first,
                &[],
                &[],
                None,
                None,
                None,
                None,
                &[],
                None,
                Some(&first_event),
                None,
                Some(&use_a),
            )
            .unwrap();
        assert!(!replay.outcome.freshly_committed);

        let omitted = store.commit_finalized_turn(0, &first).unwrap_err();
        assert!(omitted.to_string().contains("omitted or invented"));

        let redirected = holding_use(&first, &first_event, 0x71, 0x41);
        let redirected_error = match store.commit_finalized_turn_welded(
            0,
            &first,
            &[],
            &[],
            None,
            None,
            None,
            None,
            &[],
            None,
            Some(&first_event),
            None,
            Some(&redirected),
        ) {
            Err(error) => error,
            Ok(_) => panic!("redirected holding replay must refuse"),
        };
        assert!(redirected_error.to_string().contains("byte-identical"));

        let second = record(1, 1, vec![]);
        let second_event = poa_event(&store, &second);
        let second_use_same_capability = holding_use(&second, &second_event, 0x71, 0x31);
        let duplicate_error = match store.commit_finalized_turn_welded(
            1,
            &second,
            &[],
            &[],
            None,
            None,
            None,
            None,
            &[],
            None,
            Some(&second_event),
            None,
            Some(&second_use_same_capability),
        ) {
            Err(error) => error,
            Ok(_) => panic!("duplicate holding consumer must refuse"),
        };
        assert!(
            duplicate_error
                .to_string()
                .contains("already has a consumer")
        );
        assert_eq!(store.commit_cursor().unwrap(), 1);
        assert!(store.commit_record_at(1).unwrap().is_none());
        store.audit_poa_holding_consumptions().unwrap();
    }

    #[test]
    fn poa_holding_consumption_replay_refuses_invention() {
        let store = PersistentStore::open_in_memory().unwrap();
        let record = record(0, 0, vec![]);
        store.commit_finalized_turn(0, &record).unwrap();
        let event = poa_event(&store, &record);
        let invented = holding_use(&record, &event, 0x72, 0x32);
        let error = match store.commit_finalized_turn_welded(
            0,
            &record,
            &[],
            &[],
            None,
            None,
            None,
            None,
            &[],
            None,
            Some(&event),
            None,
            Some(&invented),
        ) {
            Err(error) => error,
            Ok(_) => panic!("invented holding replay must refuse"),
        };
        assert!(error.to_string().contains("omitted or invented"));
    }

    #[test]
    fn poa_holding_consumption_must_bind_the_exact_event_before_any_write() {
        let store = PersistentStore::open_in_memory().unwrap();
        let record = record(0, 0, vec![]);
        let event = poa_event(&store, &record);
        let mismatched = crate::PreparedPoaHoldingConsumptionV1::new_for_legacy_event_test(
            [0x73; 32], [0x33; 32], [0x34; 32], &record, &event, [0xEE; 32],
        )
        .unwrap();
        let error = match store.commit_finalized_turn_welded(
            0,
            &record,
            &[],
            &[],
            None,
            None,
            None,
            None,
            &[],
            None,
            Some(&event),
            None,
            Some(&mismatched),
        ) {
            Err(error) => error,
            Ok(_) => panic!("holding/event mismatch must refuse"),
        };
        assert!(error.to_string().contains("not bound"));
        assert_eq!(store.commit_cursor().unwrap(), 0);
        assert!(store.commit_record_at(0).unwrap().is_none());
        assert!(
            store
                .load_poa_event_head(event.aggregate(), b"galley-v1")
                .unwrap()
                .is_none()
        );
        assert!(
            store
                .load_poa_holding_consumption(&[0x73; 32])
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn divergent_tail_recovery_unspends_holding_for_exact_retry() {
        let store = PersistentStore::open_in_memory().unwrap();
        let empty_root = crate::canonical_ledger_root(&dregg_cell::Ledger::new());

        let mut first = record(0, 0, vec![]);
        first.ledger_root = empty_root;
        let first_event = poa_event(&store, &first);
        let first_use = holding_use(&first, &first_event, 0x74, 0x34);
        store
            .commit_finalized_turn_welded(
                0,
                &first,
                &[],
                &[],
                None,
                None,
                None,
                None,
                &[],
                None,
                Some(&first_event),
                None,
                Some(&first_use),
            )
            .unwrap();

        let mut second = record(1, 1, vec![]);
        second.ledger_root = [0xFF; 32];
        let second_event = poa_event(&store, &second);
        let second_use = holding_use(&second, &second_event, 0x75, 0x35);
        store
            .commit_finalized_turn_welded(
                1,
                &second,
                &[],
                &[],
                None,
                None,
                None,
                None,
                &[],
                None,
                Some(&second_event),
                None,
                Some(&second_use),
            )
            .unwrap();
        assert!(
            store
                .load_poa_holding_consumption(&[0x75; 32])
                .unwrap()
                .is_some()
        );

        assert_eq!(store.recover_to_last_consistent().unwrap(), 1);
        assert_eq!(store.commit_cursor().unwrap(), 1);
        assert!(
            store
                .load_poa_holding_consumption(&[0x75; 32])
                .unwrap()
                .is_none(),
            "a truncated non-final tail must release its capability nullifier"
        );

        second.ledger_root = empty_root;
        let retried = store
            .commit_finalized_turn_welded(
                1,
                &second,
                &[],
                &[],
                None,
                None,
                None,
                None,
                &[],
                None,
                Some(&second_event),
                None,
                Some(&second_use),
            )
            .unwrap();
        assert!(retried.outcome.freshly_committed);
        assert!(
            store
                .load_poa_holding_consumption(&[0x75; 32])
                .unwrap()
                .is_some()
        );
    }

    // signed-wells (ac01f9b7b): cell balances are i64; this test helper keeps a
    // u64 convenience param (callers pass small non-negative amounts) and
    // converts at the boundary.
    fn cell(seed: u8, balance: u64) -> Cell {
        Cell::with_balance([seed; 32], [seed.wrapping_add(7); 32], balance as i64)
    }

    /// A distinct 32-byte note commitment for seed `k`.
    fn note_cm(k: u8) -> [u8; 32] {
        let mut cm = [0u8; 32];
        cm[0] = 0xc0;
        cm[1] = k;
        cm
    }

    #[test]
    fn finalized_receipt_is_atomic_dense_and_byte_exact_on_replay() {
        let store = PersistentStore::open_in_memory().unwrap();
        let rec = record(0, 0, vec![]);
        let cm = note_cm(1);
        let receipt = b"executor-signed-turn-receipt";

        let fresh = store
            .commit_finalized_turn_with_notes_and_receipt(0, &rec, &[cm], 0, receipt)
            .unwrap();
        assert!(fresh.freshly_committed);
        assert_eq!(store.commit_cursor().unwrap(), 1);
        assert_eq!(store.note_count().unwrap(), 1);
        assert_eq!(store.load_receipt_chain().unwrap(), vec![receipt.to_vec()]);

        let replay = store
            .commit_finalized_turn_with_notes_and_receipt(0, &rec, &[cm], 0, receipt)
            .unwrap();
        assert!(!replay.freshly_committed);
        assert_eq!(store.note_count().unwrap(), 1);
        assert_eq!(store.receipt_chain_len().unwrap(), 1);

        assert!(matches!(
            store.commit_finalized_turn_with_notes_and_receipt(
                0,
                &rec,
                &[cm],
                0,
                b"conflicting-receipt-bytes",
            ),
            Err(StoreError::Integrity(_))
        ));
        assert_eq!(store.commit_cursor().unwrap(), 1);
        assert_eq!(store.note_count().unwrap(), 1);
        assert_eq!(store.load_receipt_chain().unwrap(), vec![receipt.to_vec()]);

        // Corrupt the table by deleting the welded entry. Replay must expose
        // the corruption, never backfill it and call the image consistent.
        let txn = store.db.begin_write().unwrap();
        {
            let mut table = txn.open_table(tables::RECEIPT_CHAIN).unwrap();
            table.remove(0).unwrap();
        }
        txn.commit().unwrap();
        assert!(matches!(
            store.commit_finalized_turn_with_notes_and_receipt(0, &rec, &[cm], 0, receipt),
            Err(StoreError::Integrity(_))
        ));
        assert_eq!(store.commit_cursor().unwrap(), 1);
        assert_eq!(store.note_count().unwrap(), 1);
        assert_eq!(store.receipt_chain_len().unwrap(), 0);
    }

    #[test]
    fn receipt_gap_aborts_entire_finalized_turn_transaction() {
        let store = PersistentStore::open_in_memory().unwrap();
        let rec = record(0, 0, vec![]);
        let cm = note_cm(2);

        let result = store.commit_finalized_turn_with_notes_and_receipt(
            0,
            &rec,
            &[cm],
            3,
            b"receipt-at-gap",
        );
        assert!(matches!(result, Err(StoreError::Integrity(_))));
        assert_eq!(store.commit_cursor().unwrap(), 0);
        assert_eq!(store.note_count().unwrap(), 0);
        assert_eq!(store.receipt_chain_len().unwrap(), 0);
        assert!(store.commit_record_at(0).unwrap().is_none());
    }

    // ── bug #58: crash-consistent note-tree weld ─────────────────────────────
    //
    // A `NoteCreate` finalized turn appends a durable note-tree leaf. Before the
    // fix, that leaf was written in its OWN redb transaction, EARLY in the node's
    // finalized-turn handler — hundreds of lines before the crash-consistent
    // `commit_finalized_turn` boundary. A crash after the note append but before
    // the commit record left the leaf durable while the turn was absent from the
    // commit log, so recovery re-applied the turn and appended the SAME leaf a
    // SECOND time. The boot path rebuilds the note tree from the durable table
    // (`load_all_note_commitments`), so the double leaf — and the diverged root —
    // was PERMANENT. The fix welds the note append into the commit transaction
    // (`commit_finalized_turn_with_notes`).

    /// FALSIFIER (RED before the fix, documenting the buggy SEQUENCING): a note
    /// leaf written in its OWN transaction, then a crash BEFORE the commit
    /// record, then recovery re-applies → the leaf lands at TWO positions and the
    /// note-tree root diverges from an exactly-once application.
    ///
    /// This models the pre-fix ordering directly (separate `store_note_commitment`
    /// + `commit_finalized_turn`) to prove the exactly-once test below is
    /// non-vacuous: it is exactly what regresses if the weld is reverted.
    #[test]
    fn crash_recovery_separate_note_txn_double_applies_the_leaf() {
        let store = PersistentStore::open_in_memory().unwrap();
        let cm = note_cm(1);
        let mut rec = record(0, 0, vec![]);
        rec.turn_hash[0] = 0x58;

        // First apply (pre-fix ordering): durable note append in its own txn …
        store
            .store_note_commitment(&dregg_cell::note::NoteCommitment(cm))
            .unwrap();
        // … then CRASH — `commit_finalized_turn` never runs, so the cursor stays 0
        // and the turn is absent from the durable commit log.
        assert_eq!(store.commit_cursor().unwrap(), 0);
        assert_eq!(store.note_count().unwrap(), 1);

        // Recovery: cursor is 0, so the turn is re-applied — and the pre-fix
        // ordering appends the SAME commitment AGAIN in its own txn.
        store
            .store_note_commitment(&dregg_cell::note::NoteCommitment(cm))
            .unwrap();
        store.commit_finalized_turn(0, &rec).unwrap();

        // The bug: two leaves for one note, a permanently diverged root.
        assert_eq!(
            store.note_count().unwrap(),
            2,
            "pre-fix sequencing double-appends across a crash-retry (this is the bug the weld fixes)"
        );
        let commitments = store.load_all_note_commitments().unwrap();
        assert_eq!(
            commitments,
            vec![
                dregg_cell::note::NoteCommitment(cm),
                dregg_cell::note::NoteCommitment(cm)
            ]
        );
    }

    /// GREEN after the fix: the note append is WELDED into the commit
    /// transaction, so a crash-retry lands the leaf at EXACTLY ONE position and
    /// the note-tree root matches an exactly-once application.
    ///
    /// Two crash shapes are covered:
    ///   (a) crash BEFORE the welded commit → nothing durable → recovery
    ///       re-applies fresh → exactly one leaf.
    ///   (b) crash AFTER the welded commit → the leaf AND the record are durable
    ///       together → an idempotent replay writes nothing → still one leaf.
    #[test]
    fn crash_recovery_welded_note_append_is_exactly_once() {
        let cm = note_cm(1);
        let mut rec = record(0, 0, vec![]);
        rec.turn_hash[0] = 0x58;

        // The CANONICAL note accumulator is the POSITION-INDEXED, append-only
        // Poseidon2 tree (`commit/src/poseidon2_tree.rs`), authored in Lean as
        // `Dregg2.Circuit.CommitmentTreeAccumulator` — which proves append is
        // genuinely ADDITIVE, so `root [cm] ≠ root [cm, cm]` (its §7
        // NON-IDEMPOTENCE guard: `root (append [1] 2) ≠ root (append (append [1] 2) 2)`).
        // A crash-retry double-apply lands TWO positional leaves, diverging that
        // root — the divergence the exactly-once weld prevents. We assert on THAT
        // root (built from the durable table via the same `commitment_to_field`
        // the node uses), plus the durable positional facts (count + ordered
        // commitment list). NOTE (surfaced finding): the store's durable
        // `note_tree_root()` is a BLAKE3 SET-tree (`dregg_commit::merkle::MerkleTree`,
        // keyed by leaf hash), so it COLLAPSES a duplicate — `root([cm]) ==
        // root([cm,cm])` — and is INSENSITIVE to a duplicate double-apply; the
        // corruption shows only in count/positions and the positional root. That
        // is exactly why the fix is transactional PREVENTION, not root-based
        // detection.
        let positional_root = |cms: &[[u8; 32]]| -> dregg_circuit::field::BabyBear {
            crate::Poseidon2NoteTree::from_blake3_commitments(cms, 4).root()
        };
        let single_leaf_root = positional_root(&[cm]);
        let double_leaf_root = positional_root(&[cm, cm]);
        assert_ne!(
            single_leaf_root, double_leaf_root,
            "positional (Lean-modeled) note-tree root MUST distinguish one leaf \
             from a double-applied duplicate (append is additive, not idempotent)"
        );

        // ── Shape (a): crash BEFORE the welded commit returns ────────────────
        let store = PersistentStore::open_in_memory().unwrap();
        // The welded commit is ONE txn. A crash before it commits leaves NOTHING
        // durable — neither the leaf nor the record — so the note is not durable
        // and the cursor is unmoved (modeled by simply not calling it).
        assert_eq!(store.note_count().unwrap(), 0);
        assert_eq!(store.commit_cursor().unwrap(), 0);

        // Recovery re-applies fresh: the welded commit writes the leaf and the
        // record together.
        let out = store
            .commit_finalized_turn_with_notes(0, &rec, &[cm])
            .unwrap();
        assert!(out.freshly_committed);
        assert_eq!(out.ordinal, 0);
        assert_eq!(
            store.note_count().unwrap(),
            1,
            "shape (a): exactly one leaf"
        );

        // ── Shape (b): the turn is FULLY committed, then re-applied (replay) ──
        // e.g. the node re-enters the handler for an already-committed turn.
        let replay = store
            .commit_finalized_turn_with_notes(0, &rec, &[cm])
            .unwrap();
        assert!(
            !replay.freshly_committed,
            "an already-committed turn must be an idempotent replay, NOT a fresh write"
        );
        assert_eq!(
            store.note_count().unwrap(),
            1,
            "shape (b): a replay must NOT re-append the note leaf"
        );

        // The durable table holds exactly ONE leaf, in order.
        let durable = store.load_all_note_commitments().unwrap();
        assert_eq!(durable, vec![dregg_cell::note::NoteCommitment(cm)]);

        // The POSITIONAL (Lean-modeled) root rebuilt from the durable table
        // equals the exactly-once single-leaf root — and NOT the double-leaf root
        // the bug produces.
        let durable_bytes: Vec<[u8; 32]> = durable.iter().map(|c| c.0).collect();
        let recovered_root = positional_root(&durable_bytes);
        assert_eq!(
            recovered_root, single_leaf_root,
            "welded exactly-once positional note-tree root must equal the single-application reference"
        );
        assert_ne!(
            recovered_root, double_leaf_root,
            "the exactly-once positional root must NOT match the double-leaf (bug) root"
        );
    }

    /// NO-REGRESSION: the normal (no-crash) path appends each turn's note exactly
    /// once, positions dense and in order, and the welded commit advances the
    /// cursor exactly as the plain path does.
    #[test]
    fn welded_note_append_normal_path_appends_once_per_turn() {
        let store = PersistentStore::open_in_memory().unwrap();
        for n in 0..4u64 {
            let mut rec = record(n, n, vec![]);
            rec.turn_hash[0] = 0x77;
            rec.turn_hash[1] = n as u8;
            let cm = note_cm(n as u8);
            let out = store
                .commit_finalized_turn_with_notes(n, &rec, &[cm])
                .unwrap();
            assert!(out.freshly_committed);
            assert_eq!(out.ordinal, n);
            assert_eq!(store.commit_cursor().unwrap(), n + 1);
            assert_eq!(store.note_count().unwrap(), n + 1);
        }
        let commitments = store.load_all_note_commitments().unwrap();
        let expected: Vec<_> = (0..4u8)
            .map(|k| dregg_cell::note::NoteCommitment(note_cm(k)))
            .collect();
        assert_eq!(
            commitments, expected,
            "one leaf per turn, dense and in order"
        );
    }

    #[test]
    fn cursor_advances_one_per_commit_and_records_round_trip() {
        let store = PersistentStore::open_in_memory().unwrap();
        assert_eq!(store.commit_cursor().unwrap(), 0);

        for n in 0..5u64 {
            let mut rec = record(n, n * 2, vec![cell(n as u8, 100 + n)]);
            rec.turn_hash[0] = 0xaa;
            rec.turn_hash[1] = n as u8;
            let assigned = store.commit_finalized_turn(n, &rec).unwrap();
            assert_eq!(assigned, n);
            assert_eq!(store.commit_cursor().unwrap(), n + 1);
        }
        assert_eq!(store.commit_log_len().unwrap(), 5);

        for n in 0..5u64 {
            let got = store.commit_record_at(n).unwrap().unwrap();
            assert_eq!(got.ordinal, n);
            assert_eq!(got.height, n + 1);
            assert_eq!(got.block_executed_up_to, n * 2);
        }
    }

    #[test]
    fn torn_state_guard_refuses_gap() {
        let store = PersistentStore::open_in_memory().unwrap();
        let mut rec = record(0, 0, vec![]);
        rec.turn_hash[0] = 1;
        store.commit_finalized_turn(0, &rec).unwrap();

        // Trying to write ordinal 2 while cursor is 1 must be refused (no gaps).
        let mut bad = record(2, 0, vec![]);
        bad.turn_hash[0] = 2;
        let err = store.commit_finalized_turn(2, &bad);
        assert!(matches!(err, Err(StoreError::Integrity(_))), "got {err:?}");
        // Cursor unchanged.
        assert_eq!(store.commit_cursor().unwrap(), 1);
    }

    #[test]
    fn idempotent_replay_of_already_committed_turn_is_noop() {
        let store = PersistentStore::open_in_memory().unwrap();
        let mut rec0 = record(0, 0, vec![cell(1, 10)]);
        rec0.turn_hash[0] = 0x11;
        let mut rec1 = record(1, 1, vec![cell(2, 20)]);
        rec1.turn_hash[0] = 0x22;
        store.commit_finalized_turn(0, &rec0).unwrap();
        store.commit_finalized_turn(1, &rec1).unwrap();

        // Re-apply ordinal 0 with the SAME turn hash: no-op success.
        let assigned = store.commit_finalized_turn(0, &rec0).unwrap();
        assert_eq!(assigned, 0);
        assert_eq!(
            store.commit_cursor().unwrap(),
            2,
            "cursor must not regress/advance"
        );

        // Re-apply ordinal 0 with a DIFFERENT turn hash: integrity error.
        let mut tampered = rec0.clone();
        tampered.turn_hash[0] = 0x99;
        let err = store.commit_finalized_turn(0, &tampered);
        assert!(matches!(err, Err(StoreError::Integrity(_))), "got {err:?}");
    }

    #[test]
    fn index_agrees_with_log_after_commits() {
        let store = PersistentStore::open_in_memory().unwrap();
        for n in 0..8u64 {
            let mut rec = record(n, n, vec![cell((n % 4) as u8, 1000 + n)]);
            rec.turn_hash[0] = 0x30;
            rec.turn_hash[1] = n as u8;
            rec.receipt_hash[0] = 0x40;
            rec.receipt_hash[1] = n as u8;
            store.commit_finalized_turn(n, &rec).unwrap();
        }
        let report = store.verify_index_agrees_with_log().unwrap();
        assert!(report.ok(), "index disagrees with log: {report:?}");
        assert_eq!(report.records, 8);
        assert_eq!(report.cursor, 8);
    }

    #[test]
    fn lookups_resolve_through_index() {
        let store = PersistentStore::open_in_memory().unwrap();
        let mut rec = record(0, 0, vec![cell(7, 555)]);
        rec.turn_hash = [0xcd; 32];
        rec.receipt_hash = [0xef; 32];
        rec.height = 42;
        rec.creator = [0x9a; 32];
        store.commit_finalized_turn(0, &rec).unwrap();

        // receipt-by-hash
        let by_receipt = store.lookup_receipt(&[0xef; 32]).unwrap().unwrap();
        assert_eq!(by_receipt.ordinal, 0);
        // turn-by-hash
        let by_turn = store.lookup_turn(&[0xcd; 32]).unwrap().unwrap();
        assert_eq!(by_turn.ordinal, 0);
        // turns-by-height
        let at_h = store.turns_at_height(42).unwrap();
        assert_eq!(at_h.len(), 1);
        assert_eq!(at_h[0].turn_hash, [0xcd; 32]);
        // turns-by-creator
        let by_creator = store.turns_by_creator(&[0x9a; 32]).unwrap();
        assert_eq!(by_creator.len(), 1);
        // cell-by-id
        let c = cell(7, 555);
        let got = store.lookup_cell(&c.id()).unwrap().unwrap();
        assert_eq!(got.state.balance(), 555);

        // Unknown keys resolve to None.
        assert!(store.lookup_receipt(&[0x00; 32]).unwrap().is_none());
        assert!(store.lookup_turn(&[0x00; 32]).unwrap().is_none());
    }

    #[test]
    fn cell_index_is_last_writer_wins() {
        let store = PersistentStore::open_in_memory().unwrap();
        // Two turns touch the SAME cell id (same seed) with different balances.
        let c_low = cell(5, 100);
        let cid = c_low.id();
        let mut rec0 = record(0, 0, vec![c_low]);
        rec0.turn_hash[0] = 1;
        store.commit_finalized_turn(0, &rec0).unwrap();

        let c_high = cell(5, 999);
        let mut rec1 = record(1, 1, vec![c_high]);
        rec1.turn_hash[0] = 2;
        store.commit_finalized_turn(1, &rec1).unwrap();

        // The index reflects the LATER writer.
        let got = store.lookup_cell(&cid).unwrap().unwrap();
        assert_eq!(got.state.balance(), 999);
        // And the index still agrees with the log under the last-writer-wins rule.
        assert!(store.verify_index_agrees_with_log().unwrap().ok());
    }

    #[test]
    fn rebuild_index_from_log_reproduces_identical_index() {
        let store = PersistentStore::open_in_memory().unwrap();
        for n in 0..6u64 {
            let mut rec = record(n, n, vec![cell((n % 3) as u8, 10 + n), cell(9, 1000 + n)]);
            rec.turn_hash[0] = 0x50;
            rec.turn_hash[1] = n as u8;
            rec.receipt_hash[0] = 0x60;
            rec.receipt_hash[1] = n as u8;
            store.commit_finalized_turn(n, &rec).unwrap();
        }
        assert!(store.verify_index_agrees_with_log().unwrap().ok());

        // Rebuild from the log alone — must replay every record and re-agree.
        let replayed = store.rebuild_index_from_log().unwrap();
        assert_eq!(replayed, 6);
        let report = store.verify_index_agrees_with_log().unwrap();
        assert!(report.ok(), "rebuilt index disagrees: {report:?}");

        // Cell 9 was written by every turn; index must hold the last (n=5) value.
        let c9 = cell(9, 1005);
        let got = store.lookup_cell(&c9.id()).unwrap().unwrap();
        assert_eq!(got.state.balance(), 1005);
    }

    /// CRASH-RECOVERY: simulate a process kill mid-write by performing a series
    /// of ATOMIC commits to an on-disk store, then dropping the store WITHOUT the
    /// next commit (the "torn" turn never lands), reopening, and asserting the
    /// store recovers to a consistent checkpoint: the cursor equals the number of
    /// turns that actually committed, every record round-trips, the index agrees
    /// with the log, and the block cursor / ledger root reflect the last
    /// committed turn (no torn state, no lost finalized turn, no double-apply).
    #[test]
    fn crash_recovery_is_consistent() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("crash.redb");

        // ── Phase 1: commit 4 turns durably, then "crash" (drop) ────────────
        {
            let store = PersistentStore::open(&path).unwrap();
            for n in 0..4u64 {
                let mut rec = record(n, n * 10, vec![cell(n as u8, 500 + n)]);
                rec.turn_hash[0] = 0x70;
                rec.turn_hash[1] = n as u8;
                rec.receipt_hash[0] = 0x80;
                rec.receipt_hash[1] = n as u8;
                rec.ledger_root = [n as u8; 32];
                store.commit_finalized_turn(n, &rec).unwrap();
            }
            // Model the crash: the 5th turn's commit transaction is begun in RAM
            // but the process dies BEFORE `commit_finalized_turn` returns. We
            // model that by simply NOT calling it, then dropping the store.
            // (redb guarantees an uncommitted txn leaves no trace.)
            drop(store);
        }

        // ── Phase 2: reopen and assert consistent recovery ─────────────────
        {
            let store = PersistentStore::open(&path).unwrap();
            // Cursor reflects exactly the committed turns.
            assert_eq!(store.commit_cursor().unwrap(), 4);
            assert_eq!(store.commit_log_len().unwrap(), 4);

            // No torn record: every ordinal in 0..cursor resolves.
            for n in 0..4u64 {
                let rec = store.commit_record_at(n).unwrap().unwrap();
                assert_eq!(rec.ordinal, n);
            }
            // The 5th (un-committed) turn left NO trace.
            assert!(store.commit_record_at(4).unwrap().is_none());

            // Index agrees with the log across the crash.
            assert!(store.verify_index_agrees_with_log().unwrap().ok());

            // Recovery anchors: block cursor + ledger root reflect the LAST
            // committed turn, never the torn one.
            assert_eq!(store.recovered_block_cursor().unwrap(), 30); // turn 3 → 3*10
            assert_eq!(store.recovered_ledger_root().unwrap(), Some([3u8; 32]));

            // ── No double-apply: re-applying turn 3 (already durable) is a
            // no-op success; the cursor does not advance. ──
            let mut rec3 = record(3, 30, vec![cell(3, 503)]);
            rec3.turn_hash[0] = 0x70;
            rec3.turn_hash[1] = 3;
            rec3.receipt_hash[0] = 0x80;
            rec3.receipt_hash[1] = 3;
            assert_eq!(store.commit_finalized_turn(3, &rec3).unwrap(), 3);
            assert_eq!(store.commit_cursor().unwrap(), 4);

            // ── Liveness: the recovered store accepts the NEXT turn at the
            // cursor and advances normally. ──
            let mut rec4 = record(4, 40, vec![cell(4, 504)]);
            rec4.turn_hash[0] = 0x70;
            rec4.turn_hash[1] = 4;
            rec4.receipt_hash[0] = 0x80;
            rec4.receipt_hash[1] = 4;
            assert_eq!(store.commit_finalized_turn(4, &rec4).unwrap(), 4);
            assert_eq!(store.commit_cursor().unwrap(), 5);
            assert!(store.verify_index_agrees_with_log().unwrap().ok());
        }
    }

    /// THE SAME-TRANSACTION BURN WELD (.docs-history-noclaude/PERSISTENCE.md): a turn's commit
    /// record and its forever-digest burns land in ONE redb transaction —
    /// after an arbitrary crash, either both are durable or neither is. The
    /// crash is modeled exactly as in `crash_recovery_is_consistent`: commits
    /// that returned are durable; everything after the last returned commit
    /// leaves no trace.
    #[test]
    fn burns_land_atomically_with_the_commit_record() {
        use crate::tables::NS_TRUSTLINE_DIGEST;

        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("burnweld.redb");
        let scope = [0x5c; 32];
        let digest = [0xd1; 32];

        {
            let store = PersistentStore::open(&path).unwrap();
            let mut rec = record(0, 0, vec![cell(1, 42)]);
            rec.turn_hash[0] = 0xb1;
            store
                .commit_finalized_turn_with_burns(0, &rec, &[(NS_TRUSTLINE_DIGEST, scope, digest)])
                .unwrap();
            // Crash before any further write.
            drop(store);
        }

        let store = PersistentStore::open(&path).unwrap();
        // BOTH halves survived: the record…
        assert_eq!(store.commit_cursor().unwrap(), 1);
        assert!(store.commit_record_at(0).unwrap().is_some());
        // …and the burn.
        assert!(
            store
                .forever_digest_seen(NS_TRUSTLINE_DIGEST, &scope, &digest)
                .unwrap(),
            "the digest burned in the commit transaction survives the crash"
        );

        // Idempotent replay re-accepts the same turn without disturbing the burn.
        let mut rec = record(0, 0, vec![cell(1, 42)]);
        rec.turn_hash[0] = 0xb1;
        assert_eq!(
            store
                .commit_finalized_turn_with_burns(0, &rec, &[(NS_TRUSTLINE_DIGEST, scope, digest)])
                .unwrap(),
            0
        );
        assert!(
            store
                .forever_digest_seen(NS_TRUSTLINE_DIGEST, &scope, &digest)
                .unwrap()
        );
    }

    /// Route-level turns commit several records at the SAME (height, creator)
    /// pair (several service turns between two attested-height advances) —
    /// the (height, creator, ordinal) key keeps every record indexed and the
    /// audit invariant exact.
    #[test]
    fn same_height_creator_records_all_index() {
        let store = PersistentStore::open_in_memory().unwrap();
        for n in 0..3u64 {
            let mut rec = record(n, 0, vec![]);
            rec.height = 7; // SAME height…
            rec.creator = [0x77; 32]; // …SAME creator
            rec.turn_hash[1] = n as u8;
            rec.receipt_hash[1] = n as u8;
            store.commit_finalized_turn(n, &rec).unwrap();
        }
        let report = store.verify_index_agrees_with_log().unwrap();
        assert!(report.ok(), "index disagrees: {report:?}");
        let at_h = store.turns_at_height(7).unwrap();
        assert_eq!(at_h.len(), 3, "all three same-(height,creator) turns index");
        let by_creator = store.turns_by_creator(&[0x77; 32]).unwrap();
        assert_eq!(by_creator.len(), 3);
    }

    /// Recovery overlay: the cell-by-id deltas committed ABOVE a checkpoint
    /// height reconstruct the post-checkpoint ledger without re-execution, and
    /// the last-writer-wins overlay re-derived from the log matches the live
    /// cell index.
    #[test]
    fn cell_overlay_since_checkpoint_matches_index() {
        let store = PersistentStore::open_in_memory().unwrap();
        // Heights 1..=6 (record(n).height == n+1). Checkpoint at height 3.
        for n in 0..6u64 {
            let mut rec = record(n, n, vec![cell((n % 2) as u8, 100 + n)]);
            rec.turn_hash[0] = 0x90;
            rec.turn_hash[1] = n as u8;
            rec.receipt_hash[0] = 0xa0;
            rec.receipt_hash[1] = n as u8;
            store.commit_finalized_turn(n, &rec).unwrap();
        }
        // Overlay above checkpoint height 3 = records with height > 3 = n>=3.
        let overlay = store.cell_overlay_since(3).unwrap();
        // Cells 0 and 1 (seeds) were both written by n in {3,4,5}; the overlay
        // holds their LATEST post-states: seed1 at n=5 (bal 105), seed0 at n=4
        // (bal 104).
        let bal = |seed: u8, b: u64| {
            let target = cell(seed, b).id();
            overlay.iter().find_map(|op| match op {
                CellOverlayOp::Upsert(c) if c.id() == target => Some(c.state.balance()),
                _ => None,
            })
        };
        assert_eq!(bal(1, 105), Some(105));
        assert_eq!(bal(0, 104), Some(104));
    }

    // =========================================================================
    // Commit-log compaction (compact_below) — the WAL-bounding tooth.
    // =========================================================================

    use dregg_cell::Ledger;

    /// Apply a resolved overlay op to a reconstructing ledger in a test:
    /// last-writer-wins upsert / tombstone remove (mirrors `node::apply_overlay_op`
    /// over the `Write = insert | remove` alphabet).
    fn apply_overlay_op_test(ledger: &mut Ledger, op: CellOverlayOp) {
        match op {
            CellOverlayOp::Upsert(c) => {
                let _ = ledger.remove(&c.id());
                let _ = ledger.insert_cell(c);
            }
            CellOverlayOp::Remove(id) => {
                let _ = ledger.remove(&id);
            }
        }
    }

    /// Reconstruct the finalized ledger AS RECOVERY DOES: the latest ledger
    /// checkpoint ⊕ `cell_overlay_since(checkpoint_height)` (last-writer-wins).
    /// This is `CrashRecovery.recover`; its root is what a recovered node
    /// reaches and MUST be invariant under compaction (`recover_eq_replay`).
    fn recovered_root(store: &PersistentStore) -> [u8; 32] {
        let cp_height = store.latest_ledger_checkpoint_height().unwrap();
        let mut ledger = match store.load_ledger_checkpoint_at(cp_height).unwrap() {
            Some(l) => l,
            None => Ledger::new(),
        };
        for op in store.cell_overlay_since(cp_height).unwrap() {
            apply_overlay_op_test(&mut ledger, op);
        }
        ledger.root()
    }

    /// Take a full-ledger checkpoint at `height` from the records committed
    /// so far whose `height <= height` (the `replay genesis (take k)` cut), and
    /// store it. Mirrors `node`'s "checkpoint the live full ledger" but built
    /// from the log so the test is self-contained. NOTE: stores via the
    /// low-level table so it does NOT co-drive compaction — the test drives
    /// `compact_below` explicitly to isolate it.
    fn checkpoint_from_log_no_codrive(store: &PersistentStore, height: u64) {
        let mut ledger = Ledger::new();
        for rec in store.commit_records_from(0).unwrap() {
            if rec.height <= height {
                for c in rec.touched_cells {
                    let _ = ledger.remove(&c.id());
                    let _ = ledger.insert_cell(c);
                }
            }
        }
        // Write the ledger checkpoint WITHOUT the checkpoint_ledger co-drive.
        let snapshot = crate::ledger_store::LedgerCheckpoint {
            height,
            cells: ledger.iter().map(|(_, c)| c.clone()).collect(),
            sovereign_commitments: Vec::new(),
            sovereign_registrations: Vec::new(),
        };
        store.store_ledger_checkpoint_snapshot(&snapshot).unwrap();
    }

    /// Commit `n` turns at heights 1..=n (record(k).height == k+1, so turn k
    /// lands at height k+1), each touching a distinct cell whose id is seeded by
    /// the turn index (so nothing is dominated and every record contributes a
    /// surviving cell to the reconstruction).
    fn commit_distinct(store: &PersistentStore, n: u64) {
        for k in 0..n {
            let mut rec = record(k, k * 10, vec![cell(k as u8, 100 + k)]);
            rec.turn_hash[0] = 0xc0;
            rec.turn_hash[1] = k as u8;
            rec.receipt_hash[0] = 0xd0;
            rec.receipt_hash[1] = k as u8;
            rec.block_id = [0xb0u8.wrapping_add(k as u8); 32];
            store.commit_finalized_turn(k, &rec).unwrap();
        }
    }

    /// **Bug #57 falsifier (persist level).** A checkpoint holds hosted cell C; a
    /// finalized turn REMOVES it (a `MakeSovereign` tombstone in `CommitRecord
    /// .removed`, no post-state). Recovery — `checkpoint ⊕ cell_overlay_since` —
    /// MUST erase C (not resurrect it as hosted) and reconstruct the recorded
    /// finalized root. The insert-only counterfactual (drop the tombstone, the
    /// pre-fix shape) RESURRECTS C and diverges from the recorded root — proving
    /// the tombstone dimension is load-bearing (the Rust twin of the Lean
    /// `insert_only_overlay_resurrects` canary).
    #[test]
    fn make_sovereign_removal_survives_recovery_not_resurrected() {
        let store = PersistentStore::open_in_memory().unwrap();
        let c = cell(0x71, 100);

        // Checkpoint at height 1 holds C HOSTED.
        let cp = crate::ledger_store::LedgerCheckpoint {
            height: 1,
            cells: vec![c.clone()],
            sovereign_commitments: Vec::new(),
            sovereign_registrations: Vec::new(),
        };
        store.store_ledger_checkpoint_snapshot(&cp).unwrap();

        // The finalized root the removing turn records commits C GONE.
        let removed_root = crate::canonical_ledger_root(&Ledger::new());

        // A committed turn at height 2 that REMOVES C — tombstone, no post-states.
        let mut rec = record(1, 0, vec![]); // record(1,..).height == 2
        rec.removed = vec![c.id().0];
        rec.ledger_root = removed_root;
        rec.turn_hash[0] = 0x57;
        store.commit_finalized_turn(0, &rec).unwrap();

        // ── GREEN pole: the overlay carries the removal → C erased, root matches.
        let mut ledger = store.load_ledger_checkpoint_at(1).unwrap().unwrap();
        assert!(
            ledger.get(&c.id()).is_some(),
            "checkpoint holds C before overlay"
        );
        for op in store.cell_overlay_since(1).unwrap() {
            apply_overlay_op_test(&mut ledger, op);
        }
        assert!(
            ledger.get(&c.id()).is_none(),
            "a MakeSovereign-removed cell must NOT be resurrected as hosted by checkpoint ⊕ overlay"
        );
        assert_eq!(
            crate::canonical_ledger_root(&ledger),
            removed_root,
            "reconstructed root must MATCH the recorded finalized root once the removal is applied"
        );

        // ── RED pole (mutation canary): an INSERT-ONLY overlay drops the tombstone
        //    → C is resurrected as hosted and the reconstructed root DIVERGES.
        let mut insert_only = store.load_ledger_checkpoint_at(1).unwrap().unwrap();
        for op in store.cell_overlay_since(1).unwrap() {
            if let CellOverlayOp::Upsert(cell) = op {
                let _ = insert_only.remove(&cell.id());
                let _ = insert_only.insert_cell(cell);
            }
            // CellOverlayOp::Remove DROPPED — the pre-fix insert-only bug.
        }
        assert!(
            insert_only.get(&c.id()).is_some(),
            "dropping the tombstone RESURRECTS the removed cell (the bug this dimension closes)"
        );
        assert_ne!(
            crate::canonical_ledger_root(&insert_only),
            removed_root,
            "the resurrected ledger root DIVERGES from the recorded finalized root — the tombstone \
             is what makes recovery converge"
        );
    }

    /// THE SAFETY TOOTH (refuse without a covering checkpoint): with NO ledger
    /// checkpoint at/above the requested height, `compact_below` deletes NOTHING
    /// — a record a checkpoint does not subsume is never removed (no lost
    /// finalized turn). The reconstruction, cursor, floor, and audit are all
    /// untouched.
    #[test]
    fn compact_below_refuses_without_a_covering_checkpoint() {
        let store = PersistentStore::open_in_memory().unwrap();
        commit_distinct(&store, 5); // heights 1..=5
        let before = recovered_root(&store);
        let cursor_before = store.commit_cursor().unwrap();
        let len_before = store.commit_log_len().unwrap();

        // No checkpoint at all → refuse (no-op), 0 compacted.
        assert_eq!(store.compact_below(3).unwrap(), 0);

        // A checkpoint exists but BELOW the requested height → still refuse:
        // it does not subsume records up to height 4.
        checkpoint_from_log_no_codrive(&store, 2); // covers heights ≤2 only
        assert_eq!(
            store.compact_below(4).unwrap(),
            0,
            "checkpoint at 2 does NOT cover a compact_below(4) — must refuse"
        );

        // Nothing changed.
        assert_eq!(store.commit_log_len().unwrap(), len_before);
        assert_eq!(store.commit_cursor().unwrap(), cursor_before);
        assert_eq!(store.commit_compacted_floor().unwrap(), 0);
        assert_eq!(recovered_root(&store), before);
        let report = store.verify_index_agrees_with_log().unwrap();
        assert!(report.ok(), "audit must hold after a refusal: {report:?}");
    }

    /// THE COMPACTION TOOTH: a record BELOW a covering checkpoint IS compacted,
    /// the ledger STILL reconstructs to the same root, and the durable cursor is
    /// UNCHANGED. reconstruct-after-compact == reconstruct-before-compact.
    #[test]
    fn compact_below_removes_subsumed_records_preserving_reconstruction_and_cursor() {
        let store = PersistentStore::open_in_memory().unwrap();
        commit_distinct(&store, 6); // heights 1..=6, ordinals 0..6
        let root_before = recovered_root(&store);
        let cursor_before = store.commit_cursor().unwrap();
        assert_eq!(cursor_before, 6);

        // A covering checkpoint at height 3 (subsumes records with height ≤ 3 =
        // ordinals 0,1,2 → heights 1,2,3). compact_below(3) removes the records
        // STRICTLY below height 3 = heights 1,2 = ordinals 0,1.
        checkpoint_from_log_no_codrive(&store, 3);
        let compacted = store.compact_below_with_test_poa_anchor_v1(3).unwrap();
        assert_eq!(compacted, 2, "heights 1 and 2 are strictly below 3");

        // Physical records dropped by 2; the CURSOR is unchanged; the floor rose.
        assert_eq!(store.commit_log_len().unwrap(), 4);
        assert_eq!(
            store.commit_cursor().unwrap(),
            cursor_before,
            "the durable applied high-water mark must NOT move under compaction"
        );
        assert_eq!(store.commit_compacted_floor().unwrap(), 2);

        // The compacted ordinals are physically gone; the survivors remain dense.
        assert!(store.commit_record_at(0).unwrap().is_none());
        assert!(store.commit_record_at(1).unwrap().is_none());
        for o in 2..6 {
            assert_eq!(store.commit_record_at(o).unwrap().unwrap().ordinal, o);
        }

        // THE EQUIVALENCE: reconstruction is byte-for-byte identical.
        assert_eq!(
            recovered_root(&store),
            root_before,
            "checkpoint ⊕ overlay after compaction must equal the pre-compaction ledger"
        );
        // The head record (cursor-1) — recovery's anchors — is intact.
        assert_eq!(
            store
                .commit_record_at(cursor_before - 1)
                .unwrap()
                .unwrap()
                .ordinal,
            5
        );
        assert_eq!(store.recovered_block_cursor().unwrap(), 5 * 10);
        assert_eq!(
            store.recovered_ledger_root().unwrap().unwrap(),
            store.commit_record_at(5).unwrap().unwrap().ledger_root
        );
    }

    /// THE INDEX-AUDIT INVARIANT holds post-compaction: the compacted records'
    /// receipt / turn / (height,creator) entries are gone (no orphans), the
    /// cell-by-id index is the surviving log's last-writer-wins projection, and
    /// the compaction-aware density `cursor == records + compacted` holds.
    /// Lookups for survivors still resolve; lookups for compacted turns 404.
    #[test]
    fn index_audit_holds_after_compaction() {
        let store = PersistentStore::open_in_memory().unwrap();
        commit_distinct(&store, 6);
        // Grab a compacted turn's and a surviving turn's hashes before compaction.
        let compacted_turn = store.commit_record_at(0).unwrap().unwrap();
        let surviving_turn = store.commit_record_at(4).unwrap().unwrap();

        checkpoint_from_log_no_codrive(&store, 3);
        assert_eq!(store.compact_below_with_test_poa_anchor_v1(3).unwrap(), 2);

        let report = store.verify_index_agrees_with_log().unwrap();
        assert!(report.ok(), "audit must hold after compaction: {report:?}");
        assert_eq!(report.records, 4, "4 survivors physically present");
        assert_eq!(report.compacted, 2);
        assert_eq!(report.cursor, 6, "cursor unchanged == records + compacted");

        // A compacted turn no longer resolves through the (removed) index entry…
        assert!(
            store
                .lookup_turn(&compacted_turn.turn_hash)
                .unwrap()
                .is_none()
        );
        assert!(
            store
                .lookup_receipt(&compacted_turn.receipt_hash)
                .unwrap()
                .is_none()
        );
        // …but a survivor still does.
        assert_eq!(
            store
                .lookup_turn(&surviving_turn.turn_hash)
                .unwrap()
                .unwrap()
                .ordinal,
            4
        );

        // Rebuilding the index from the (compacted) log re-agrees — the rebuild
        // is over the survivors and stays consistent.
        let replayed = store.rebuild_index_from_log().unwrap();
        assert_eq!(replayed, 4);
        assert!(store.verify_index_agrees_with_log().unwrap().ok());
    }

    /// NO DOUBLE-APPLY across compaction: a compacted turn's `block_id` is
    /// retained, so `commit_log_block_ids` (the identity execution cursor's turn
    /// half) still reports EVERY applied turn — the returned id set is invariant
    /// under compaction. A compacted turn therefore never looks un-executed.
    #[test]
    fn compaction_preserves_the_applied_turn_identity_set() {
        let store = PersistentStore::open_in_memory().unwrap();
        commit_distinct(&store, 6);
        let ids_before: std::collections::HashSet<[u8; 32]> =
            store.commit_log_block_ids().unwrap().into_iter().collect();
        assert_eq!(ids_before.len(), 6);

        checkpoint_from_log_no_codrive(&store, 3);
        assert_eq!(store.compact_below_with_test_poa_anchor_v1(3).unwrap(), 2);

        let ids_after: std::collections::HashSet<[u8; 32]> =
            store.commit_log_block_ids().unwrap().into_iter().collect();
        assert_eq!(
            ids_after, ids_before,
            "the applied-turn id set must be INVARIANT under compaction \
             (else a compacted turn re-executes on top of the checkpoint)"
        );
    }

    /// Per-cell receipt provenance spans compaction and removals. The removing
    /// turn becomes the durable head even though the cell has no hosted
    /// post-state, and that head survives after both carrying records are gone.
    #[test]
    fn per_cell_receipt_head_compaction_preserves_removal_provenance() {
        let store = PersistentStore::open_in_memory().unwrap();
        let a = cell(0x75, 100);
        let a_id = a.id();

        let mut create = record(0, 0, vec![a]);
        create.receipt_hash = [0xA1; 32];
        create.turn_hash = [0xB1; 32];
        store.commit_finalized_turn(0, &create).unwrap();

        let mut remove = record(1, 0, vec![]);
        remove.receipt_hash = [0xA2; 32];
        remove.turn_hash = [0xB2; 32];
        remove.removed = vec![a_id.0];
        store.commit_finalized_turn(1, &remove).unwrap();

        let before = store.load_per_cell_receipt_head_recovery_v1().unwrap();
        let head = before
            .current
            .iter()
            .find(|head| head.cell == a_id)
            .unwrap();
        assert_eq!(head.writer_ordinal, 1);
        assert_eq!(head.receipt_hash, [0xA2; 32]);

        store
            .store_ledger_checkpoint_snapshot(&crate::LedgerCheckpoint {
                height: 3,
                cells: Vec::new(),
                sovereign_commitments: Vec::new(),
                sovereign_registrations: Vec::new(),
            })
            .unwrap();
        assert_eq!(store.compact_below_with_test_poa_anchor_v1(3).unwrap(), 2);

        let after = store.load_per_cell_receipt_head_recovery_v1().unwrap();
        assert!(after.live_records.is_empty());
        let baseline = after
            .baseline
            .iter()
            .find(|head| head.cell == a_id)
            .unwrap();
        let current = after.current.iter().find(|head| head.cell == a_id).unwrap();
        assert_eq!(baseline, current);
        assert_eq!(current.writer_ordinal, 1);
        assert_eq!(current.receipt_hash, [0xA2; 32]);
    }

    /// A single current map cannot pass this test. The doomed live writer of X
    /// must roll back to X's compacted predecessor, while an unrelated surviving
    /// live record gives root recovery its last-good convergence point.
    #[test]
    fn divergent_tail_recovery_restores_compacted_per_cell_predecessor() {
        let store = PersistentStore::open_in_memory().unwrap();
        let x = cell(0x76, 100);
        let y = cell(0x77, 200);
        let x_id = x.id();

        let mut ledger = Ledger::new();
        ledger.insert_cell(x.clone()).unwrap();
        let mut x_create = record(0, 0, vec![x.clone()]);
        x_create.receipt_hash = [0xC1; 32];
        x_create.turn_hash = [0xD1; 32];
        x_create.ledger_root = crate::canonical_ledger_root(&ledger);
        store.commit_finalized_turn(0, &x_create).unwrap();

        ledger.insert_cell(y.clone()).unwrap();
        let mut y_create = record(1, 0, vec![y.clone()]);
        y_create.receipt_hash = [0xC2; 32];
        y_create.turn_hash = [0xD2; 32];
        y_create.ledger_root = crate::canonical_ledger_root(&ledger);
        store.commit_finalized_turn(1, &y_create).unwrap();

        store
            .store_ledger_checkpoint_snapshot(&crate::LedgerCheckpoint {
                height: 2,
                cells: vec![x.clone(), y],
                sovereign_commitments: Vec::new(),
                sovereign_registrations: Vec::new(),
            })
            .unwrap();
        assert_eq!(store.compact_below_with_test_poa_anchor_v1(2).unwrap(), 1);

        let mut poisoned_x = x;
        assert!(poisoned_x.state.credit_balance(1));
        let mut bad = record(2, 0, vec![poisoned_x]);
        bad.receipt_hash = [0xC3; 32];
        bad.turn_hash = [0xD3; 32];
        bad.ledger_root = [0xDE; 32];
        store.commit_finalized_turn(2, &bad).unwrap();
        let before = store.load_per_cell_receipt_head_recovery_v1().unwrap();
        assert_eq!(
            before
                .current
                .iter()
                .find(|head| head.cell == x_id)
                .unwrap()
                .receipt_hash,
            [0xC3; 32]
        );

        assert_eq!(store.recover_to_last_consistent().unwrap(), 1);
        let after = store.load_per_cell_receipt_head_recovery_v1().unwrap();
        let restored = after.current.iter().find(|head| head.cell == x_id).unwrap();
        assert_eq!(restored.writer_ordinal, 0);
        assert_eq!(restored.receipt_hash, [0xC1; 32]);
        assert!(store.verify_index_agrees_with_log().unwrap().ok());
    }

    /// A checkpoint alone is not deletion authority. It remains durable while unsigned
    /// compaction refuses; a subsequent genuine hybrid anchor drives the same safe prefix.
    #[test]
    fn checkpoint_ledger_refuses_unsigned_compaction_then_signed_anchor_drives_it() {
        let store = PersistentStore::open_in_memory().unwrap();
        commit_distinct(&store, 6); // heights 1..=6
        let root_before = recovered_root(&store);

        // Build the FULL live ledger (what node passes to checkpoint_ledger).
        let mut full = Ledger::new();
        for rec in store.commit_records_from(0).unwrap() {
            for c in rec.touched_cells {
                let _ = full.remove(&c.id());
                let _ = full.insert_cell(c);
            }
        }
        // The checkpoint is durable, but its old automatic call has no signed anchor and must
        // delete nothing.
        store.checkpoint_ledger(&full, 6).unwrap();
        assert_eq!(store.commit_compacted_floor().unwrap(), 0);
        assert_eq!(store.commit_log_len().unwrap(), 6);

        assert_eq!(store.compact_below_with_test_poa_anchor_v1(6).unwrap(), 5);

        assert_eq!(
            store.commit_compacted_floor().unwrap(),
            5,
            "the signed anchor compacted the 5 records below height 6"
        );
        assert_eq!(store.commit_log_len().unwrap(), 1, "only height-6 survives");
        assert_eq!(store.commit_cursor().unwrap(), 6, "cursor unchanged");
        assert!(store.verify_index_agrees_with_log().unwrap().ok());
        assert_eq!(
            recovered_root(&store),
            root_before,
            "co-driven compaction preserves the recovered ledger"
        );
    }

    /// Compaction is CRASH-DURABLE: after compaction + reopen, the floor, the
    /// cursor, the survivors, the retained compacted ids, and the audit all
    /// survive the restart (one redb transaction = one fsync boundary).
    #[test]
    fn compaction_survives_reopen() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("compact.redb");

        let (root_before, head_root): ([u8; 32], [u8; 32]);
        {
            let store = PersistentStore::open(&path).unwrap();
            commit_distinct(&store, 6);
            root_before = recovered_root(&store);
            head_root = store.commit_record_at(5).unwrap().unwrap().ledger_root;
            checkpoint_from_log_no_codrive(&store, 4);
            assert_eq!(store.compact_below_with_test_poa_anchor_v1(4).unwrap(), 3); // heights 1,2,3
            drop(store);
        }

        let store = PersistentStore::open_with_test_poa_compact_trust_v1(&path).unwrap();
        // Durable post-compaction state.
        assert_eq!(store.commit_compacted_floor().unwrap(), 3);
        assert_eq!(store.commit_log_len().unwrap(), 3);
        assert_eq!(store.commit_cursor().unwrap(), 6);
        // The audit (compaction-aware density) holds across the reopen.
        let report = store.verify_index_agrees_with_log().unwrap();
        assert!(report.ok(), "audit after reopen: {report:?}");
        // The recovered ledger is unchanged across the compaction + restart.
        assert_eq!(recovered_root(&store), root_before);
        assert_eq!(store.recovered_ledger_root().unwrap(), Some(head_root));
        // The applied-turn identity set survived (no-double-apply across restart).
        assert_eq!(store.commit_log_block_ids().unwrap().len(), 6);
    }

    /// compact_below stops at the FIRST record at/above `height` — it removes a
    /// contiguous ordinal PREFIX only, never punching a gap into the live log,
    /// and never removing a record the overlay still needs (height ≥ the cut).
    #[test]
    fn compact_below_removes_only_the_contiguous_below_prefix() {
        let store = PersistentStore::open_in_memory().unwrap();
        commit_distinct(&store, 6); // heights 1..=6
        // Cover up to height 6, but only ask to compact below height 4.
        checkpoint_from_log_no_codrive(&store, 6);
        let compacted = store.compact_below_with_test_poa_anchor_v1(4).unwrap();
        // heights 1,2,3 are strictly below 4 → ordinals 0,1,2 removed; the
        // record at height 4 (ordinal 3) and above survive.
        assert_eq!(compacted, 3);
        assert_eq!(store.commit_compacted_floor().unwrap(), 3);
        assert!(store.commit_record_at(2).unwrap().is_none());
        assert_eq!(store.commit_record_at(3).unwrap().unwrap().height, 4);
        // The live log [3,6) is dense — no gap.
        for o in 3..6 {
            assert!(store.commit_record_at(o).unwrap().is_some());
        }
        assert!(store.verify_index_agrees_with_log().unwrap().ok());

        // A second compaction at the same height is an idempotent no-op (the
        // below-prefix is already gone).
        assert_eq!(store.compact_below_with_test_poa_anchor_v1(4).unwrap(), 0);
        assert_eq!(store.commit_compacted_floor().unwrap(), 3);
    }

    /// Anti-vacuity: an over-broad deletion (dropping a record the overlay still
    /// needs) WOULD change the reconstruction — proving the height<cut guard is
    /// load-bearing, mirroring `CrashRecovery.lost_turn_changes_state`. Here we
    /// confirm that compacting a record whose cell is NOT dominated and is NOT
    /// in the checkpoint would lose it — so `compact_below` must (and does)
    /// refuse to touch records at/above the covering checkpoint's reach.
    #[test]
    fn keeping_overlay_records_is_load_bearing() {
        let store = PersistentStore::open_in_memory().unwrap();
        commit_distinct(&store, 6); // distinct cells per height → none dominated
        let full = recovered_root(&store);

        // Checkpoint at height 3 covers heights ≤3. Records at heights 4,5,6 are
        // the overlay and are LOAD-BEARING (distinct, undominated cells).
        checkpoint_from_log_no_codrive(&store, 3);
        assert_eq!(store.compact_below_with_test_poa_anchor_v1(3).unwrap(), 2); // only heights 1,2 go

        // The overlay records (4,5,6) are untouched and the ledger is intact.
        assert_eq!(recovered_root(&store), full);
        assert!(store.commit_record_at(3).unwrap().is_some()); // height 4 survives
        assert!(store.commit_record_at(5).unwrap().is_some()); // height 6 survives

        // And compact_below can NEVER be asked to remove them while the only
        // checkpoint is at 3: a request below height 4 leaves them; a request at
        // height 5 is REFUSED (checkpoint at 3 does not cover it).
        assert_eq!(store.compact_below(5).unwrap(), 0);
        assert_eq!(recovered_root(&store), full);
    }

    // =========================================================================
    // recover_to_last_consistent — RECOVER a torn/divergent image, never strand
    // =========================================================================

    /// Commit `n` turns at ascending heights, each touching a DISTINCT cell, with
    /// every record's `ledger_root` set to the canonical (v3) root of the
    /// reconstructed prefix THROUGH that turn — i.e. a genuine, self-consistent
    /// log where `recover_to_last_consistent` finds the head converging.
    fn commit_canonical(store: &PersistentStore, n: u64) {
        let mut ledger = Ledger::new();
        for k in 0..n {
            let c = cell(k as u8, 100 + k);
            let _ = ledger.remove(&c.id());
            let _ = ledger.insert_cell(c.clone());
            let mut rec = record(k, k * 10, vec![c]);
            rec.turn_hash[0] = 0xe0;
            rec.turn_hash[1] = k as u8;
            rec.receipt_hash[0] = 0xf0;
            rec.receipt_hash[1] = k as u8;
            // The TRUE post-state root the convergence check (and recovery) uses.
            rec.ledger_root = crate::canonical_ledger_root(&ledger);
            store.commit_finalized_turn(k, &rec).unwrap();
        }
    }

    /// A consistent image is left UNTOUCHED: `recover_to_last_consistent` is a
    /// no-op (0 truncated) when the head already reconstructs to its recorded
    /// root, and the convergence check (last record's root == reconstruction)
    /// holds before and after.
    #[test]
    fn recover_is_a_noop_on_a_consistent_image() {
        let store = PersistentStore::open_in_memory().unwrap();
        commit_canonical(&store, 5);
        let cursor_before = store.commit_cursor().unwrap();

        assert_eq!(
            store.recover_to_last_consistent().unwrap(),
            0,
            "a consistent image needs no truncation"
        );
        assert_eq!(store.commit_cursor().unwrap(), cursor_before);
        assert!(store.verify_index_agrees_with_log().unwrap().ok());
    }

    /// THE STRAND-PREVENTION TOOTH: a TORN write leaves the log's tail
    /// inconsistent with its recorded root (the old path would refuse the whole
    /// image and STRAND the owner). `recover_to_last_consistent` finds the last
    /// root-converging ordinal, TRUNCATES the divergent tail, and the image then
    /// opens at the last-good state — recovery succeeds where refusal stranded.
    #[test]
    fn recover_truncates_a_divergent_tail_to_last_good() {
        let store = PersistentStore::open_in_memory().unwrap();
        // Three genuine, self-consistent turns (ordinals 0,1,2).
        commit_canonical(&store, 3);

        // Model a TORN write: append two more records whose `ledger_root` does
        // NOT match the reconstruction (a crash mid-write / a poisoned cell left
        // the recorded root inconsistent with the post-state). They land in the
        // log (cursor advances), but the head no longer reconstructs to its claim.
        for k in 3..5u64 {
            let c = cell(k as u8, 100 + k);
            let mut bad = record(k, k * 10, vec![c]);
            bad.turn_hash[0] = 0xe0;
            bad.turn_hash[1] = k as u8;
            bad.receipt_hash[0] = 0xf0;
            bad.receipt_hash[1] = k as u8;
            // A WRONG root — the tear: the post-state does not match this claim.
            bad.ledger_root = [0xde; 32];
            store.commit_finalized_turn(k, &bad).unwrap();
        }
        assert_eq!(store.commit_cursor().unwrap(), 5);
        // Sanity: the head (ordinal 4) does NOT converge — the old check refuses.
        let head_root = store.recovered_ledger_root().unwrap().unwrap();
        assert_eq!(head_root, [0xde; 32], "the torn tail recorded a bogus root");

        // RECOVER: truncate the two divergent records, land at the last-good (2).
        let truncated = store.recover_to_last_consistent().unwrap();
        assert_eq!(truncated, 2, "the two torn records are dropped");
        assert_eq!(
            store.commit_cursor().unwrap(),
            3,
            "cursor regresses to last-good + 1"
        );
        assert!(store.commit_record_at(3).unwrap().is_none(), "tail dropped");
        assert!(store.commit_record_at(4).unwrap().is_none(), "tail dropped");
        assert!(
            store.commit_record_at(2).unwrap().is_some(),
            "last-good kept"
        );

        // THE CONVERGENCE CHECK NOW PASSES at the recovered point: the head's
        // recorded root equals the reconstruction (this is what `recover` asserts).
        let mut ledger = Ledger::new();
        for op in store.cell_overlay_since(0).unwrap() {
            apply_overlay_op_test(&mut ledger, op);
        }
        assert_eq!(
            crate::canonical_ledger_root(&ledger),
            store.recovered_ledger_root().unwrap().unwrap(),
            "after recovery the reconstruction MATCHES the head's recorded root \
             (the integrity check passes — the image opens instead of stranding)"
        );

        // The index agrees with the truncated log, and the recovered store is
        // LIVE: it accepts the next turn at the recovered cursor.
        assert!(store.verify_index_agrees_with_log().unwrap().ok());
        let c5 = cell(5, 105);
        let mut next = record(5, 50, vec![c5]);
        next.turn_hash[0] = 0xe0;
        next.turn_hash[1] = 9;
        next.receipt_hash[0] = 0xf0;
        next.receipt_hash[1] = 9;
        next.ledger_root = [0x5a; 32];
        assert_eq!(
            store.commit_finalized_turn(3, &next).unwrap(),
            3,
            "the recovered store accepts the NEXT turn at the recovered cursor"
        );
    }

    /// Recovery survives a real reopen (on-disk redb): commit a consistent
    /// prefix, "crash" with a divergent tail, drop, reopen, `recover_to_last_
    /// consistent`, and confirm the truncation is durable.
    #[test]
    fn recover_truncation_is_durable_across_reopen() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("recover.redb");
        {
            let store = PersistentStore::open(&path).unwrap();
            commit_canonical(&store, 3);
            // Torn tail: one bogus-root record.
            let c = cell(3, 103);
            let mut bad = record(3, 30, vec![c]);
            bad.turn_hash[0] = 0xe0;
            bad.turn_hash[1] = 3;
            bad.receipt_hash[0] = 0xf0;
            bad.receipt_hash[1] = 3;
            bad.ledger_root = [0xab; 32];
            store.commit_finalized_turn(3, &bad).unwrap();
            drop(store);
        }
        let store = PersistentStore::open(&path).unwrap();
        assert_eq!(store.commit_cursor().unwrap(), 4, "torn tail is on disk");
        assert_eq!(store.recover_to_last_consistent().unwrap(), 1);
        assert_eq!(store.commit_cursor().unwrap(), 3);
        drop(store);

        // The truncation persisted: a fresh reopen sees the recovered cursor.
        let store = PersistentStore::open(&path).unwrap();
        assert_eq!(store.commit_cursor().unwrap(), 3);
        assert!(store.commit_record_at(3).unwrap().is_none());
        assert!(store.verify_index_agrees_with_log().unwrap().ok());
    }

    /// A genesis BASELINE: cells genesis established (fee well, issuer well,
    /// faucet) that NO turn touches — they live only in the baseline, never in a
    /// commit record nor (at sub-checkpoint height) a checkpoint. High seeds so
    /// they never collide with the per-turn `cell(k, …)` ids (k small).
    fn genesis_baseline() -> Ledger {
        let mut g = Ledger::new();
        for seed in [0xf0u8, 0xf1, 0xf2] {
            let _ = g.insert_cell(cell(seed, 1_000_000));
        }
        g
    }

    /// Like `commit_canonical` but each record's `ledger_root` is the canonical
    /// root over the GENESIS BASELINE ⊕ the touched cells through that turn — the
    /// real shape a node commits (the recorded root commits the FULL ledger, not
    /// just the touched delta).
    fn commit_canonical_over(store: &PersistentStore, genesis: &Ledger, n: u64) {
        let mut ledger = genesis.clone();
        for k in 0..n {
            let c = cell(k as u8, 100 + k);
            let _ = ledger.remove(&c.id());
            let _ = ledger.insert_cell(c.clone());
            let mut rec = record(k, k * 10, vec![c]);
            rec.turn_hash[0] = 0xc0;
            rec.turn_hash[1] = k as u8;
            rec.receipt_hash[0] = 0xd0;
            rec.receipt_hash[1] = k as u8;
            rec.ledger_root = crate::canonical_ledger_root(&ledger);
            store.commit_finalized_turn(k, &rec).unwrap();
        }
    }

    /// THE SUB-CHECKPOINT POWER-CYCLE TOOTH (the real homelab bug): a node that
    /// finalized turns BELOW its first ledger checkpoint has untouched genesis
    /// cells the commit-log overlay does NOT carry. The recorded `ledger_root`
    /// commits the FULL ledger (genesis ⊕ touched), so reconstructing from an
    /// EMPTY base mismatches at EVERY ordinal — the no-baseline walk finds no
    /// converging prefix and FALSELY refuses a perfectly consistent image as
    /// unsalvageable. Reconstructing on the genesis baseline converges: a clean
    /// image is a no-op (0 truncated), never a store-integrity fatal.
    #[test]
    fn recover_from_base_does_not_falsely_strand_a_sub_checkpoint_image() {
        let store = PersistentStore::open_in_memory().unwrap();
        let genesis = genesis_baseline();
        // A genuinely CONSISTENT log over a non-empty baseline — no torn tail.
        commit_canonical_over(&store, &genesis, 5);
        let cursor_before = store.commit_cursor().unwrap();

        // The no-baseline walk MISreads this consistent image as unsalvageable:
        // every record's root commits genesis ⊕ touched, which the empty-base
        // reconstruction can never reproduce. (This is the bug the fix removes.)
        assert!(
            matches!(
                store.recover_to_last_consistent(),
                Err(StoreError::Integrity(_))
            ),
            "no-baseline reconstruction falsely refuses a consistent sub-checkpoint image"
        );

        // The genesis-baseline walk converges at the head: clean image, 0 dropped.
        assert_eq!(
            store
                .recover_to_last_consistent_from_base(&genesis)
                .unwrap(),
            0,
            "a consistent image over its genesis baseline needs NO truncation \
             (no false store-integrity fatal on a power-cycle restart)"
        );
        assert_eq!(
            store.commit_cursor().unwrap(),
            cursor_before,
            "cursor untouched on a consistent image"
        );
        assert!(store.verify_index_agrees_with_log().unwrap().ok());
    }

    /// A TORN TAIL over a genesis baseline recovers cleanly: the consistent
    /// prefix (reconstructed genesis ⊕ overlay) is kept, the torn records (bogus
    /// recorded root) are truncated, and the post-recovery reconstruction MATCHES
    /// the head's recorded root — the integrity check passes, the image opens.
    #[test]
    fn recover_from_base_truncates_a_torn_tail_over_genesis() {
        let store = PersistentStore::open_in_memory().unwrap();
        let genesis = genesis_baseline();
        commit_canonical_over(&store, &genesis, 3);

        // Model the abrupt power loss mid-write: two records land (cursor
        // advances) whose recorded root does NOT match the post-state (a torn /
        // poisoned tail), so the head no longer reconstructs to its claim.
        for k in 3..5u64 {
            let c = cell(k as u8, 100 + k);
            let mut bad = record(k, k * 10, vec![c]);
            bad.turn_hash[0] = 0xc0;
            bad.turn_hash[1] = k as u8;
            bad.receipt_hash[0] = 0xd0;
            bad.receipt_hash[1] = k as u8;
            bad.ledger_root = [0xde; 32]; // the tear: a root the post-state never reaches
            store.commit_finalized_turn(k, &bad).unwrap();
        }
        assert_eq!(store.commit_cursor().unwrap(), 5);

        let truncated = store
            .recover_to_last_consistent_from_base(&genesis)
            .unwrap();
        assert_eq!(truncated, 2, "the two torn records are dropped");
        assert_eq!(
            store.commit_cursor().unwrap(),
            3,
            "cursor regresses to last-good + 1"
        );
        assert!(
            store.commit_record_at(2).unwrap().is_some(),
            "last-good kept"
        );
        assert!(store.commit_record_at(3).unwrap().is_none(), "tail dropped");

        // THE CONVERGENCE CHECK PASSES at the recovered point — reconstructing
        // genesis ⊕ overlay (the SOUND `reseed_genesis_then_overlay` order)
        // equals the head's recorded root, so the node opens instead of stranding.
        let mut ledger = genesis.clone();
        for op in store.cell_overlay_since(0).unwrap() {
            apply_overlay_op_test(&mut ledger, op);
        }
        assert_eq!(
            crate::canonical_ledger_root(&ledger),
            store.recovered_ledger_root().unwrap().unwrap(),
            "post-recovery reconstruction matches the head's recorded root"
        );
        assert!(store.verify_index_agrees_with_log().unwrap().ok());
    }

    /// FAIL-CLOSED on GENUINE corruption: when NO prefix reconstructs to its
    /// recorded root even WITH the genesis baseline in place (a real divergence /
    /// tamper, not a torn tail with a recoverable prefix), recovery refuses with
    /// a store-integrity error rather than silently laundering corruption into an
    /// empty image. The baseline fix never weakens fail-closed.
    #[test]
    fn recover_from_base_fails_closed_on_genuine_corruption() {
        let store = PersistentStore::open_in_memory().unwrap();
        let genesis = genesis_baseline();

        // Every record carries a bogus recorded root — no prefix (even genesis ⊕
        // overlay) reconstructs to any claim. There is NO salvageable last-good
        // point: this is real divergence, not a torn tail.
        for k in 0..3u64 {
            let c = cell(k as u8, 100 + k);
            let mut bad = record(k, k * 10, vec![c]);
            bad.turn_hash[0] = 0xc0;
            bad.turn_hash[1] = k as u8;
            bad.receipt_hash[0] = 0xd0;
            bad.receipt_hash[1] = k as u8;
            bad.ledger_root = [0x5e ^ k as u8; 32]; // divergent at every ordinal
            store.commit_finalized_turn(k, &bad).unwrap();
        }

        assert!(
            matches!(
                store.recover_to_last_consistent_from_base(&genesis),
                Err(StoreError::Integrity(_))
            ),
            "genuine corruption (no converging prefix) must FAIL CLOSED, never \
             silently recover to an empty image"
        );
        // Fail-closed = untouched: the cursor did not regress, nothing truncated.
        assert_eq!(store.commit_cursor().unwrap(), 3, "no silent truncation");
    }

    /// Commit `n` turns over `genesis`, each touching a distinct cell, with every
    /// record's root the TRUE root except that `mutate(k, &mut record)` may
    /// corrupt one. Returns the true per-ordinal roots.
    fn commit_over_with(
        store: &PersistentStore,
        genesis: &Ledger,
        n: u64,
        mutate: impl Fn(u64, &mut CommitRecord),
    ) -> Vec<[u8; 32]> {
        let mut ledger = genesis.clone();
        let mut roots = Vec::new();
        for k in 0..n {
            let c = cell(k as u8, 100 + k);
            let _ = ledger.remove(&c.id());
            let _ = ledger.insert_cell(c.clone());
            let mut rec = record(k, k * 10, vec![c]);
            rec.turn_hash[0] = 0x90;
            rec.turn_hash[1] = k as u8;
            rec.receipt_hash[0] = 0x91;
            rec.receipt_hash[1] = k as u8;
            rec.ledger_root = crate::canonical_ledger_root(&ledger);
            roots.push(rec.ledger_root);
            mutate(k, &mut rec);
            store.commit_finalized_turn(k, &rec).unwrap();
        }
        roots
    }

    /// ⚑ F3 — a corrupted `ledger_root` in the MIDDLE of the log is refused,
    /// naming the ordinal. Pre-fix, the walk evaluated ordinal 2, did not record
    /// the miss, matched 3 and 4, and returned `Ok(0)`: "consistent". The
    /// mutation is asserted present and the head asserted convergent first.
    #[test]
    fn recover_refuses_a_corrupt_intermediate_root_naming_the_ordinal() {
        let store = PersistentStore::open_in_memory().unwrap();
        let genesis = genesis_baseline();
        let roots = commit_over_with(&store, &genesis, 5, |k, rec| {
            if k == 2 {
                rec.ledger_root[31] ^= 0x80;
            }
        });

        let middle = store.commit_record_at(2).unwrap().unwrap();
        assert_ne!(middle.ledger_root, roots[2], "the mutation must be present");
        assert_eq!(
            store.recovered_ledger_root().unwrap(),
            Some(roots[4]),
            "the head converges — the head-only check passes this image"
        );

        match store.recover_to_last_consistent_from_base(&genesis) {
            Err(StoreError::IntermediateRootMismatch {
                ordinal,
                height,
                converged_at,
            }) => {
                assert_eq!(ordinal, 2);
                assert_eq!(height, middle.height);
                assert_eq!(converged_at, 3);
            }
            other => panic!("expected IntermediateRootMismatch at ordinal 2, got {other:?}"),
        }
        assert_eq!(store.commit_cursor().unwrap(), 5, "refused, not truncated");
    }

    /// ⚑ F3 — the other shape lane 12 named: record `k` carries corrupted
    /// `touched_cells` (its recorded root is honest) and a later record
    /// overwrites the same cell, so the head reconverges.
    #[test]
    fn recover_refuses_corrupt_touched_cells_a_later_record_overwrites() {
        let store = PersistentStore::open_in_memory().unwrap();
        let genesis = genesis_baseline();
        let mut ledger = genesis.clone();
        let shared = |balance: u64| cell(0x42, balance);
        let mut last_root = [0u8; 32];
        for k in 0..4u64 {
            let honest = shared(1_000 + k);
            let _ = ledger.remove(&honest.id());
            let _ = ledger.insert_cell(honest.clone());
            let mut rec = record(k, k * 10, vec![honest]);
            rec.turn_hash[0] = 0x92;
            rec.turn_hash[1] = k as u8;
            rec.receipt_hash[0] = 0x93;
            rec.receipt_hash[1] = k as u8;
            rec.ledger_root = crate::canonical_ledger_root(&ledger);
            last_root = rec.ledger_root;
            if k == 1 {
                // The recorded root is honest; the stored post-state is not.
                rec.touched_cells = vec![shared(9_999_999)];
            }
            store.commit_finalized_turn(k, &rec).unwrap();
        }
        let middle = store.commit_record_at(1).unwrap().unwrap();
        assert_eq!(
            middle.touched_cells,
            vec![shared(9_999_999)],
            "mutation present"
        );
        assert_eq!(store.recovered_ledger_root().unwrap(), Some(last_root));

        assert!(
            matches!(
                store.recover_to_last_consistent_from_base(&genesis),
                Err(StoreError::IntermediateRootMismatch {
                    ordinal: 1,
                    converged_at: 2,
                    ..
                })
            ),
            "a corrupt intermediate post-state must be refused even though record 2 hides it"
        );
    }

    /// ⚑ F3 at the node's boot shape: EMPTY base, the genesis baseline pinned as
    /// a height-0 checkpoint. Records above the checkpoint are checkable; the
    /// same corruption is refused by the no-argument walk the node calls.
    #[test]
    fn recover_over_a_checkpoint_refuses_a_corrupt_intermediate_root() {
        let store = PersistentStore::open_in_memory().unwrap();
        let genesis = genesis_baseline();
        store.checkpoint_ledger(&genesis, 0).unwrap();
        // `record(k, ..)` puts ordinal k at height k + 1: every record is above
        // the height-0 checkpoint.
        let roots = commit_over_with(&store, &genesis, 4, |k, rec| {
            if k == 1 {
                rec.ledger_root = [0x77; 32];
            }
        });
        assert_ne!(
            store.commit_record_at(1).unwrap().unwrap().ledger_root,
            roots[1]
        );
        assert_eq!(store.recovered_ledger_root().unwrap(), Some(roots[3]));
        assert!(matches!(
            store.recover_to_last_consistent(),
            Err(StoreError::IntermediateRootMismatch { ordinal: 1, .. })
        ));

        // The honest image over the same checkpoint is untouched: 0 truncated.
        let clean = PersistentStore::open_in_memory().unwrap();
        clean.checkpoint_ledger(&genesis, 0).unwrap();
        commit_over_with(&clean, &genesis, 4, |_, _| {});
        assert_eq!(clean.recover_to_last_consistent().unwrap(), 0);

        // And a TORN TAIL over it is still recovered, not refused: a suffix of
        // misses with no later match is what a crash leaves.
        let torn = PersistentStore::open_in_memory().unwrap();
        torn.checkpoint_ledger(&genesis, 0).unwrap();
        commit_over_with(&torn, &genesis, 4, |k, rec| {
            if k >= 2 {
                rec.ledger_root = [0x66; 32];
            }
        });
        assert_eq!(torn.recover_to_last_consistent().unwrap(), 2);
        assert_eq!(torn.commit_cursor().unwrap(), 2);
    }

    /// THE SINGLE-WRITER GUARD (against the OTHER corruption cause — concurrent
    /// writers): redb holds an exclusive advisory file lock per database file, so
    /// a SECOND process/handle opening the SAME durable image while the first
    /// holds it is REJECTED with a store error — it can never tear the file with a
    /// racing double-write. (This is why login's logout RELEASES the durable
    /// handle before a re-login reopens it, and why a fork is ephemeral.) A torn
    /// commit log from two cockpit processes on one image is thus prevented at the
    /// source: fail (the second open errors), never corrupt.
    #[test]
    fn a_second_concurrent_open_is_rejected_not_corrupting() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("single-writer.redb");

        // First handle commits a turn and stays OPEN (holding the lock).
        let first = PersistentStore::open(&path).unwrap();
        let mut rec = record(0, 0, vec![cell(1, 42)]);
        rec.turn_hash[0] = 0x11;
        first.commit_finalized_turn(0, &rec).unwrap();

        // A second open of the SAME file while `first` is alive must be REFUSED —
        // redb's single-writer lock fails-closed (no tearing double-write).
        let second = PersistentStore::open(&path);
        assert!(
            second.is_err(),
            "a concurrent open of the same durable image must be rejected (single-writer)"
        );

        // After the first handle is RELEASED, a reopen succeeds and the committed
        // turn is intact (the rejection protected, not corrupted, the image).
        drop(first);
        let reopened = PersistentStore::open(&path).unwrap();
        assert_eq!(reopened.commit_cursor().unwrap(), 1);
        assert!(reopened.commit_record_at(0).unwrap().is_some());
    }

    #[test]
    fn faithful_root_weld_survives_restart_with_exact_attestation() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("faithful-live.redb");
        let signer = FaithfulSigner::new(0x21);
        let block_id = [0x31; 32];
        let notes = [[0x41; 32], [0x42; 32]];
        let expected_root;
        {
            let store = PersistentStore::open(&path).unwrap();
            let commit = faithful_commit_record(0, block_id);
            let (anchor, edge) = plan_test_edge(&store, 1, block_id, &notes);
            expected_root = edge.successor;
            let envelope = signer.sign_edge(edge.clone());
            let attested = test_attested(&signer, &commit, &edge);
            let outcome = store
                .commit_finalized_turn_with_faithful_root(
                    0,
                    &commit,
                    &notes,
                    0,
                    b"receipt-0",
                    FinalizedFaithfulRootWeld {
                        initial_anchor: Some(&anchor),
                        envelope: &envelope,
                        author_committee: &[signer.ed_pk],
                        author_ml_dsa_committee: std::slice::from_ref(&signer.pq_pk),
                        attested_root: &attested,
                        spent_nullifiers: &[],
                        finalized_spends: &[],
                    },
                )
                .unwrap();
            assert!(outcome.freshly_committed);
            assert_eq!(store.note_count().unwrap(), 2);
            let replay = store
                .commit_finalized_turn_with_faithful_root(
                    0,
                    &commit,
                    &notes,
                    0,
                    b"receipt-0",
                    FinalizedFaithfulRootWeld {
                        initial_anchor: Some(&anchor),
                        envelope: &envelope,
                        author_committee: &[signer.ed_pk],
                        author_ml_dsa_committee: std::slice::from_ref(&signer.pq_pk),
                        attested_root: &attested,
                        spent_nullifiers: &[],
                        finalized_spends: &[],
                    },
                )
                .unwrap();
            assert!(!replay.freshly_committed);
            assert_eq!(store.note_count().unwrap(), 2);
        }

        let reopened = PersistentStore::open(&path).unwrap();
        let root = reopened.latest_attested_root().unwrap().unwrap();
        assert_eq!(root.note_tree_root, Some(expected_root.to_bytes()));
        let history = reopened
            .load_faithful_note_root_history_hybrid(
                &[signer.ed_pk],
                std::slice::from_ref(&signer.pq_pk),
                1,
                crate::FaithfulNoteRootExpectationV1 {
                    records: 1,
                    height: 1,
                    note_count: 2,
                    root: expected_root,
                },
            )
            .unwrap();
        assert_eq!(history.head().root, expected_root);
        assert_eq!(reopened.commit_cursor().unwrap(), 1);
        assert_eq!(reopened.receipt_chain_len().unwrap(), 1);
    }

    #[test]
    fn exact_fnsp_v3_bootstrap_derives_only_from_faithful_records_and_restarts() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("exact-v3-faithful-bootstrap.redb");
        let spends = [
            FinalizedNullifierRecord {
                nullifier: [0x91; 32],
                value: 91,
            },
            FinalizedNullifierRecord {
                nullifier: [0x92; 32],
                value: 92,
            },
        ];
        let expected_records: Vec<_> = spends
            .iter()
            .enumerate()
            .map(
                |(seq, spend)| dregg_circuit::exact_nullifier_aafi::ExactAppendRecord {
                    seq: u64::try_from(seq).unwrap(),
                    raw: spend.nullifier,
                    value: spend.value,
                },
            )
            .collect();
        let expected_head;
        {
            let store = PersistentStore::open(&path).unwrap();
            let write = store.db.begin_write().unwrap();
            append_fresh_nullifiers_in(&write, &spends, 0).unwrap();
            write.commit().unwrap();
            expected_head = store
                .initialize_exact_fnsp_v3_state_from_faithful_nullifiers()
                .unwrap();
            assert_eq!(
                store.exact_fnsp_v3_append_records().unwrap(),
                Some(expected_records.clone())
            );
        }

        let reopened = PersistentStore::open(&path).unwrap();
        assert_eq!(
            reopened.exact_fnsp_v3_state_head().unwrap(),
            Some(expected_head)
        );
        assert_eq!(
            reopened.exact_fnsp_v3_append_records().unwrap(),
            Some(expected_records)
        );
        let write = reopened.db.begin_write().unwrap();
        validate_exact_fnsp_v3_faithful_prefix_in(&write).unwrap();
        write.abort().unwrap();
    }

    #[test]
    fn activated_exact_epoch_allows_nonspend_but_refuses_faithful_only_spend_growth() {
        let store = PersistentStore::open_in_memory().unwrap();
        install_test_exact_activation(&store);
        let signer = FaithfulSigner::new(0x38);

        // Advancing the faithful height without a spend remains legal: exact-v3 shadows the
        // ordered nullifier history, not unrelated note/root-only turns.
        //
        // Both receipts are CANONICAL executor-signed rows. Past the activation the receipt
        // authority is live (`stage_receipt_head_on_append_in`), so an opaque byte string is no
        // longer an admissible receipt — this fixture used to append `b"post-activation-nonspend"`
        // and the store correctly refused it as `FrameReceiptMismatch` before the property under
        // test was ever reached.
        let first_block = [0x39; 32];
        let first_commit = faithful_commit_record(0, first_block);
        let (first_receipt, _) = test_activated_receipt(&first_commit, None);
        let (first_anchor, first_edge) = plan_test_edge(&store, 1, first_block, &[]);
        let first_envelope = signer.sign_edge(first_edge.clone());
        let first_attested = test_attested(&signer, &first_commit, &first_edge);
        let first = store
            .commit_finalized_turn_with_faithful_root(
                0,
                &first_commit,
                &[],
                0,
                &first_receipt,
                FinalizedFaithfulRootWeld {
                    initial_anchor: Some(&first_anchor),
                    envelope: &first_envelope,
                    author_committee: std::slice::from_ref(&signer.ed_pk),
                    author_ml_dsa_committee: std::slice::from_ref(&signer.pq_pk),
                    attested_root: &first_attested,
                    spent_nullifiers: &[],
                    finalized_spends: &[],
                },
            )
            .expect("nonspend height may advance");
        assert!(first.freshly_committed);

        // The same generic path may no longer grow the nullifier history after activation.  It
        // must use the exact frame/CAS writer, and refusal leaves every would-be row absent.
        let spend = FinalizedNullifierRecord {
            nullifier: [0x3a; 32],
            value: 0x3a,
        };
        let second_block = [0x3b; 32];
        let second_commit = faithful_commit_record(1, second_block);
        let (second_receipt, _) = test_activated_receipt(&second_commit, None);
        let (second_anchor, second_edge) = plan_test_edge(&store, 2, second_block, &[]);
        let second_envelope = signer.sign_edge(second_edge.clone());
        let successor = store
            .plan_faithful_nullifier_successor(std::slice::from_ref(&spend))
            .unwrap();
        let second_attested =
            test_attested_with_nullifier_root(&signer, &second_commit, &second_edge, successor);
        let statements =
            test_finalized_spend_inputs(&store, &second_anchor, std::slice::from_ref(&spend));
        assert!(matches!(
            store.commit_finalized_turn_with_faithful_root(
                1,
                &second_commit,
                &[],
                1,
                &second_receipt,
                FinalizedFaithfulRootWeld {
                    initial_anchor: None,
                    envelope: &second_envelope,
                    author_committee: std::slice::from_ref(&signer.ed_pk),
                    author_ml_dsa_committee: std::slice::from_ref(&signer.pq_pk),
                    attested_root: &second_attested,
                    spent_nullifiers: std::slice::from_ref(&spend),
                    finalized_spends: &statements,
                },
            ),
            Err(StoreError::Integrity(ref message)) if message.contains("requires the exact frame/CAS weld")
        ));
        assert_eq!(store.commit_cursor().unwrap(), 1);
        assert!(store.commit_record_at(1).unwrap().is_none());
        assert_eq!(store.receipt_chain_len().unwrap(), 1);
        assert!(store.load_faithful_nullifier_records().unwrap().is_empty());
    }

    #[test]
    fn first_exact_frame_atomically_installs_full_weld_over_nonempty_prefix() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("exact-frc1.redb");
        let store = PersistentStore::open(&path).unwrap();
        let prefix = FinalizedNullifierRecord {
            nullifier: [0x81; 32],
            value: 81,
        };
        let write = store.db.begin_write().unwrap();
        append_fresh_nullifiers_in(&write, std::slice::from_ref(&prefix), 0).unwrap();
        write.commit().unwrap();
        let initial = store
            .initialize_exact_fnsp_v3_state_from_faithful_nullifiers()
            .unwrap();
        assert_eq!(initial.generation(), 1);

        let spend = FinalizedNullifierRecord {
            nullifier: [0x82; 32],
            value: 82,
        };
        let exact = store
            .prepare_exact_fnsp_v3_append(spend.nullifier, spend.value)
            .unwrap();
        let unrelated = store.prepare_exact_fnsp_v3_append([0x83; 32], 83).unwrap();
        let key = dregg_types::SigningKey::from_bytes(&[0x84; 32]);
        let block_id = [0x85; 32];
        let mut commit = faithful_commit_record(0, block_id);
        let receipt = dregg_turn::TurnReceipt {
            turn_hash: commit.turn_hash,
            forest_hash: [0x86; 32],
            pre_state_hash: [0x87; 32],
            post_state_hash: [0x88; 32],
            timestamp: 1_700_000_000,
            agent: dregg_cell::CellId(commit.creator),
            federation_id: faithful_context().1,
            finality: dregg_turn::Finality::Final,
            ..Default::default()
        };
        let (activation, frame, encoded_receipt) =
            crate::exact_fnsp_v3_frame_head::exact_fnsp_v3_test_first_frame_bundle(
                &store,
                exact,
                &key,
                receipt.clone(),
            );
        let (_, mismatched_frame, _) =
            crate::exact_fnsp_v3_frame_head::exact_fnsp_v3_test_first_frame_bundle(
                &store, unrelated, &key, receipt,
            );
        commit.receipt_hash = frame.full_receipt_hash();

        // Current exact-v3 is a solo epoch: the activation executor is also the independently
        // pinned hybrid author whose evidence reauthenticates FRC1 at restart.
        let signer = FaithfulSigner::new(0x84);
        let (anchor, edge) = plan_test_edge(&store, 1, block_id, &[]);
        let envelope = signer.sign_edge(edge.clone());
        let successor = store
            .plan_faithful_nullifier_successor(std::slice::from_ref(&spend))
            .unwrap();
        let attested = test_attested_with_nullifier_root(&signer, &commit, &edge, successor);
        let statements = test_finalized_spend_inputs(&store, &anchor, std::slice::from_ref(&spend));
        let weld = || FinalizedFaithfulRootWeld {
            initial_anchor: Some(&anchor),
            envelope: &envelope,
            author_committee: std::slice::from_ref(&signer.ed_pk),
            author_ml_dsa_committee: std::slice::from_ref(&signer.pq_pk),
            attested_root: &attested,
            spent_nullifiers: std::slice::from_ref(&spend),
            finalized_spends: &statements,
        };
        let rate_bytes = dregg_turn::executor::RateLimitStateSnapshot {
            counts: vec![dregg_turn::executor::RateLimitCountEntry {
                cell: dregg_cell::CellId([0x91; 32]),
                sender: [0x92; 32],
                epoch: 3,
                count: 4,
            }],
            sums: Vec::new(),
        }
        .to_canonical_bytes()
        .unwrap();
        let descriptor = dregg_cell::FactoryDescriptor {
            factory_vk: [0x93; 32],
            child_program_vk: None,
            child_vk_strategy: None,
            allowed_cap_templates: Vec::new(),
            field_constraints: Vec::new(),
            state_constraints: Vec::new(),
            default_mode: dregg_cell::CellMode::Hosted,
            creation_budget: None,
        };
        let factory_bytes = dregg_cell::factory::FactoryRegistrySnapshot {
            current_epoch: 3,
            descriptors: vec![dregg_cell::factory::FactoryDescriptorEntry {
                factory_vk: descriptor.factory_vk,
                descriptor,
            }],
            creation_counts: Vec::new(),
        }
        .to_canonical_bytes()
        .unwrap();
        let executor_state = crate::FinalizedExecutorConsensusState {
            accumulators: crate::ExecutorAccumulatorSnapshot {
                bridged_nullifiers: vec![[0x94; 32]],
                ..Default::default()
            },
            rate_limit_snapshot: Some(rate_bytes.clone()),
            factory_registry_snapshot: Some(factory_bytes.clone()),
            reactive_nullifiers: crate::ReactiveNullifierCasV1::new(
                crate::reactive_nullifier_commitment(&[]),
                vec![[0x95; 32]],
            ),
            ..Default::default()
        };

        // The activation is staged inside the final exact helper.  A later frame/exact mismatch
        // drops the sole writer, so even the activation row and earlier commit/receipt writes are
        // unobservable.
        assert!(
            store
                .commit_finalized_turn_with_faithful_root_and_exact_fnsp_v3_frame(
                    0,
                    &commit,
                    0,
                    &encoded_receipt,
                    weld(),
                    exact,
                    mismatched_frame,
                    Some(activation.clone()),
                    &executor_state,
                )
                .is_err()
        );
        assert!(store.exact_fnsp_v3_activation().unwrap().is_none());
        assert_eq!(store.commit_cursor().unwrap(), 0);
        assert!(store.commit_record_at(0).unwrap().is_none());
        assert_eq!(store.receipt_chain_len().unwrap(), 0);
        assert!(store.faithful_note_root_head().unwrap().is_none());
        assert!(store.latest_attested_root().unwrap().is_none());
        assert_eq!(store.exact_fnsp_v3_state_head().unwrap(), Some(initial));
        assert_eq!(
            store.load_executor_accumulator_snapshot().unwrap(),
            crate::ExecutorAccumulatorSnapshot::default()
        );
        assert!(
            store
                .load_latest_rate_limit_snapshot_bytes()
                .unwrap()
                .is_none()
        );
        assert!(
            store
                .load_latest_factory_registry_snapshot_bytes()
                .unwrap()
                .is_none()
        );
        assert!(store.load_reactive_nullifier_keys().unwrap().is_empty());
        assert_eq!(
            store.load_faithful_nullifier_records().unwrap(),
            vec![(
                dregg_cell::note::Nullifier(prefix.nullifier),
                prefix.value,
                0
            )]
        );

        let fresh = store
            .commit_finalized_turn_with_faithful_root_and_exact_fnsp_v3_frame(
                0,
                &commit,
                0,
                &encoded_receipt,
                weld(),
                exact,
                frame.clone(),
                Some(activation.clone()),
                &executor_state,
            )
            .expect("full atomic first frame");
        assert!(fresh.outcome.freshly_committed);
        let fresh_core_id = fresh.finalized_receipt_core_id;
        let (loaded_core_id, loaded_core) = store
            .finalized_receipt_core_v1(0)
            .unwrap()
            .expect("fresh exact frame has durable semantic core");
        assert_eq!(loaded_core_id, fresh_core_id);
        assert_eq!(loaded_core.context().block_id(), block_id);
        assert_eq!(loaded_core.context().tau_round(), commit.height);
        assert_eq!(
            loaded_core.context().consensus_unix_seconds(),
            1_700_000_000
        );
        assert_eq!(
            loaded_core.predecessor(),
            dregg_turn::FinalizedReceiptPredecessorV1::Genesis
        );
        assert_eq!(
            fresh.committed_head.exact_after().generation(),
            initial.generation() + 1
        );
        assert_eq!(store.commit_cursor().unwrap(), 1);
        assert_eq!(store.receipt_chain_len().unwrap(), 1);
        assert_eq!(
            store.exact_fnsp_v3_state_head().unwrap(),
            Some(exact.successor())
        );
        assert_eq!(
            store
                .exact_fnsp_v3_activation()
                .unwrap()
                .unwrap()
                .activation_hash(),
            activation.activation_hash()
        );
        assert_eq!(store.load_faithful_nullifier_records().unwrap().len(), 2);
        assert!(store.faithful_note_root_head().unwrap().is_some());
        assert!(store.latest_attested_root().unwrap().is_some());
        assert_eq!(
            store.load_executor_accumulator_snapshot().unwrap(),
            executor_state.accumulators
        );
        assert_eq!(
            store.load_latest_rate_limit_snapshot_bytes().unwrap(),
            Some(rate_bytes)
        );
        assert_eq!(
            store.load_latest_factory_registry_snapshot_bytes().unwrap(),
            Some(factory_bytes)
        );
        assert_eq!(
            store.load_reactive_nullifier_keys().unwrap(),
            vec![[0x95; 32]]
        );

        let mut altered_executor_state = executor_state.clone();
        altered_executor_state
            .accumulators
            .bridged_nullifiers
            .push([0x96; 32]);
        assert!(
            store
                .commit_finalized_turn_with_faithful_root_and_exact_fnsp_v3_frame(
                    0,
                    &commit,
                    0,
                    &encoded_receipt,
                    weld(),
                    exact,
                    frame.clone(),
                    Some(activation.clone()),
                    &altered_executor_state,
                )
                .is_err(),
            "replay may not alter executor side state"
        );

        let replay = store
            .commit_finalized_turn_with_faithful_root_and_exact_fnsp_v3_frame(
                0,
                &commit,
                0,
                &encoded_receipt,
                weld(),
                exact,
                frame,
                Some(activation),
                &executor_state,
            )
            .expect("byte-identical first-frame replay");
        assert!(!replay.outcome.freshly_committed);
        assert_eq!(replay.finalized_receipt_core_id, fresh_core_id);
        assert_eq!(store.commit_cursor().unwrap(), 1);
        assert_eq!(store.receipt_chain_len().unwrap(), 1);
        assert_eq!(store.load_faithful_nullifier_records().unwrap().len(), 2);

        store
            .store_ledger_checkpoint_snapshot(&crate::LedgerCheckpoint {
                height: 2,
                cells: Vec::new(),
                sovereign_commitments: Vec::new(),
                sovereign_registrations: Vec::new(),
            })
            .unwrap();
        assert_eq!(store.compact_below_with_test_poa_anchor_v1(2).unwrap(), 1);
        assert!(store.commit_record_at(0).unwrap().is_none());

        drop(store);
        let reopened = PersistentStore::open_with_test_poa_compact_trust_v1(&path)
            .expect("restart reauthenticates FRC1");
        assert_eq!(
            reopened.finalized_receipt_core_v1(0).unwrap().unwrap().0,
            fresh_core_id
        );
        assert_eq!(
            reopened
                .finalized_receipt_core_v1_by_id(fresh_core_id)
                .unwrap()
                .unwrap()
                .0,
            0,
            "typed semantic identity resolves to the same receipt coordinate after restart"
        );

        let write = reopened.db.begin_write().unwrap();
        {
            let mut by_id = write
                .open_table(crate::finalized_receipt_core_v1::FINALIZED_RECEIPT_INDEX_BY_CORE_V1)
                .unwrap();
            by_id.insert(&fresh_core_id.bytes(), 1).unwrap();
        }
        write.commit().unwrap();
        assert!(
            reopened
                .finalized_receipt_core_v1_by_id(fresh_core_id)
                .is_err(),
            "a mismatched reverse coordinate must fail at query time"
        );

        let write = reopened.db.begin_write().unwrap();
        {
            let mut by_id = write
                .open_table(crate::finalized_receipt_core_v1::FINALIZED_RECEIPT_INDEX_BY_CORE_V1)
                .unwrap();
            by_id.insert(&fresh_core_id.bytes(), 0).unwrap();
        }
        {
            let mut by_index = write
                .open_table(
                    crate::finalized_receipt_core_v1::FINALIZED_RECEIPT_CORE_BY_RECEIPT_INDEX_V1,
                )
                .unwrap();
            by_index.insert(1, &fresh_core_id.bytes()).unwrap();
        }
        write.commit().unwrap();
        drop(reopened);
        assert!(
            PersistentStore::open_with_test_poa_compact_trust_v1(&path).is_err(),
            "restart audit must refuse one semantic id indexed at two receipt coordinates"
        );
    }

    /// BOTH poles of the faithful/exact boot gate, in ONE process and over ONE store.
    ///
    /// The gate is an equality between two authorities, and an equality between two EMPTY
    /// authorities holds for free — so the admitting pole asserts that records actually exist on
    /// both sides.  The refusing pole then advances the exact authority ALONE in the same live
    /// store and requires the gate to refuse by variant.
    #[test]
    fn faithful_exact_boot_gate_admits_the_honest_image_and_refuses_one_sided_growth() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("both-poles.redb");
        {
            let store = PersistentStore::open(&path).unwrap();
            let activation = install_test_exact_frame_activation(&store);
            commit_test_exact_frame_turn(
                &store,
                &activation,
                0,
                [0xA1; 32],
                FinalizedNullifierRecord {
                    nullifier: [0x66; 32],
                    value: 66,
                },
                None,
                None,
            );
        }

        // POLE 1 — the honest production image REOPENS, and the equality that let it through is
        // between two NON-EMPTY histories.
        let reopened = PersistentStore::open(&path).expect("honest production image reopens");
        assert_eq!(reopened.faithful_nullifier_record_count().unwrap(), 1);
        assert_eq!(
            reopened
                .exact_fnsp_v3_append_records()
                .unwrap()
                .expect("exact authority")
                .len(),
            1
        );
        let write = reopened.db.begin_write().unwrap();
        validate_exact_fnsp_v3_faithful_prefix_in(&write)
            .expect("both authorities describe the same append history");
        write.abort().unwrap();

        // POLE 2 — advance the EXACT authority alone in that same store.  This is precisely what
        // a narrow exact-append seam used to leave behind durably, and the gate must refuse it.
        let candidate = reopened
            .prepare_exact_fnsp_v3_append([0x67; 32], 67)
            .unwrap();
        let write = reopened.db.begin_write().unwrap();
        let (write, _) = crate::exact_fnsp_v3_state::compare_and_commit_exact_fnsp_v3_append_in(
            write, candidate,
        )
        .unwrap();
        let refusal = validate_exact_fnsp_v3_faithful_prefix_in(&write);
        assert!(
            matches!(refusal, Err(StoreError::Integrity(ref message)) if message.contains("diverges")),
            "one-sided exact growth must be refused, got {refusal:?}"
        );
        write.abort().unwrap();

        // The refused transaction mutated nothing, so the honest store still opens.
        drop(reopened);
        let again = PersistentStore::open(&path).expect("refusal left the honest image intact");
        assert_eq!(again.faithful_nullifier_record_count().unwrap(), 1);
        assert_eq!(
            again
                .exact_fnsp_v3_append_records()
                .unwrap()
                .expect("exact authority")
                .len(),
            1
        );
    }

    #[test]
    fn exact_fnsp_v3_prefix_gate_refuses_empty_mismatched_and_reordered_authorities() {
        fn assert_refused(
            legacy: &[FinalizedNullifierRecord],
            exact: impl IntoIterator<Item = dregg_circuit::exact_nullifier_aafi::ExactAppendRecord>,
        ) {
            let store = PersistentStore::open_in_memory().unwrap();
            let write = store.db.begin_write().unwrap();
            append_fresh_nullifiers_in(&write, legacy, 0).unwrap();
            write.commit().unwrap();
            store
                .initialize_unaudited_exact_fnsp_v3_state(exact)
                .unwrap();
            let write = store.db.begin_write().unwrap();
            assert!(matches!(
                validate_exact_fnsp_v3_faithful_prefix_in(&write),
                Err(StoreError::Integrity(ref message)) if message.contains("diverges")
            ));
            write.abort().unwrap();
        }

        let a = FinalizedNullifierRecord {
            nullifier: [0x93; 32],
            value: 930,
        };
        let b = FinalizedNullifierRecord {
            nullifier: [0x94; 32],
            value: 940,
        };

        // The exact-v3 authority may not start empty beside existing v2/legacy spends.
        assert_refused(std::slice::from_ref(&a), std::iter::empty());

        // Equal lengths are insufficient: raw key and full value both belong to the prefix.
        assert_refused(
            std::slice::from_ref(&a),
            [dregg_circuit::exact_nullifier_aafi::ExactAppendRecord {
                seq: 0,
                raw: [0x95; 32],
                value: a.value + 1,
            }],
        );

        // Both images are individually dense and valid, but exchanging append positions changes
        // the protocol history and must refuse.
        assert_refused(
            &[a, b],
            [
                dregg_circuit::exact_nullifier_aafi::ExactAppendRecord {
                    seq: 0,
                    raw: b.nullifier,
                    value: b.value,
                },
                dregg_circuit::exact_nullifier_aafi::ExactAppendRecord {
                    seq: 1,
                    raw: a.nullifier,
                    value: a.value,
                },
            ],
        );
    }

    #[test]
    fn exact_fnsp_v3_finalized_weld_replays_historical_turn_after_restart() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("faithful-exact-v3-live-boundary.redb");
        let signer = FaithfulSigner::new(0x41);
        let block_id = [0xa1; 32];
        let notes = [[0xb1; 32]];
        let spend = FinalizedNullifierRecord {
            nullifier: [0xc1; 32],
            value: 4_242,
        };
        let expected_exact_head;
        let expected_latest_note_root;
        let replay_commit;
        let replay_anchor;
        let replay_envelope;
        let replay_attested;
        let replay_finalized_spends;

        {
            let store = PersistentStore::open(&path).unwrap();
            store
                .initialize_exact_fnsp_v3_state_from_faithful_nullifiers()
                .unwrap();
            let exact = store
                .prepare_exact_fnsp_v3_append(spend.nullifier, spend.value)
                .unwrap();
            let first_exact_head = exact.successor();

            let commit = faithful_commit_record(0, block_id);
            let (anchor, edge) = plan_test_edge(&store, 1, block_id, &notes);
            let envelope = signer.sign_edge(edge.clone());
            let expected_legacy_root = store
                .plan_faithful_nullifier_successor(std::slice::from_ref(&spend))
                .unwrap();
            let attested =
                test_attested_with_nullifier_root(&signer, &commit, &edge, expected_legacy_root);
            let finalized_spends =
                test_finalized_spend_inputs(&store, &anchor, std::slice::from_ref(&spend));
            replay_commit = commit.clone();
            replay_anchor = anchor.clone();
            replay_envelope = envelope.clone();
            replay_attested = attested.clone();
            replay_finalized_spends = finalized_spends.clone();
            let weld = || FinalizedFaithfulRootWeld {
                initial_anchor: Some(&anchor),
                envelope: &envelope,
                author_committee: std::slice::from_ref(&signer.ed_pk),
                author_ml_dsa_committee: std::slice::from_ref(&signer.pq_pk),
                attested_root: &attested,
                spent_nullifiers: std::slice::from_ref(&spend),
                finalized_spends: &finalized_spends,
            };

            let unrelated = store
                .prepare_exact_fnsp_v3_append([0xee; 32], spend.value + 1)
                .unwrap();
            assert!(matches!(
                store.commit_finalized_turn_with_faithful_root_and_exact_fnsp_v3(
                    0,
                    &commit,
                    &notes,
                    0,
                    b"receipt-exact-v3",
                    weld(),
                    unrelated,
                ),
                Err(StoreError::Integrity(ref message))
                    if message.contains("does not name the finalized turn")
            ));
            assert_eq!(store.commit_cursor().unwrap(), 0);
            assert_eq!(store.note_count().unwrap(), 0);
            assert_eq!(store.receipt_chain_len().unwrap(), 0);
            assert_eq!(
                store.exact_fnsp_v3_state_head().unwrap(),
                Some(exact.expected())
            );

            let outcome = store
                .commit_finalized_turn_with_faithful_root_and_exact_fnsp_v3(
                    0,
                    &commit,
                    &notes,
                    0,
                    b"receipt-exact-v3",
                    weld(),
                    exact,
                )
                .unwrap();
            assert!(outcome.freshly_committed);
            assert_eq!(store.commit_cursor().unwrap(), 1);
            assert_eq!(store.note_count().unwrap(), 1);
            assert_eq!(store.receipt_chain_len().unwrap(), 1);
            assert_eq!(
                store.exact_fnsp_v3_state_head().unwrap(),
                Some(first_exact_head)
            );
            assert_eq!(
                store.exact_fnsp_v3_append_records().unwrap(),
                Some(vec![exact.append_record()])
            );

            let replay = store
                .commit_finalized_turn_with_faithful_root_and_exact_fnsp_v3(
                    0,
                    &commit,
                    &notes,
                    0,
                    b"receipt-exact-v3",
                    weld(),
                    exact,
                )
                .unwrap();
            assert!(!replay.freshly_committed);
            assert_eq!(
                store.exact_fnsp_v3_append_records().unwrap().unwrap().len(),
                1
            );

            // Advance both authorities, notes, receipt history, and the faithful edge once more.
            // The post-restart replay below must verify A at its historical prefix rather than
            // incorrectly demanding that A still be the current tail.
            let later_notes = [[0xb3; 32]];
            let later_spend = FinalizedNullifierRecord {
                nullifier: [0xc3; 32],
                value: 5_353,
            };
            let later_exact = store
                .prepare_exact_fnsp_v3_append(later_spend.nullifier, later_spend.value)
                .unwrap();
            expected_exact_head = later_exact.successor();
            let later_block = [0xa3; 32];
            let later_commit = faithful_commit_record(1, later_block);
            let (later_anchor, later_edge) = plan_test_edge(&store, 2, later_block, &later_notes);
            expected_latest_note_root = later_edge.successor;
            let later_envelope = signer.sign_edge(later_edge.clone());
            let later_legacy_root = store
                .plan_faithful_nullifier_successor(std::slice::from_ref(&later_spend))
                .unwrap();
            let later_attested = test_attested_with_nullifier_root(
                &signer,
                &later_commit,
                &later_edge,
                later_legacy_root,
            );
            let later_finalized_spends = test_finalized_spend_inputs(
                &store,
                &later_anchor,
                std::slice::from_ref(&later_spend),
            );
            let later_outcome = store
                .commit_finalized_turn_with_faithful_root_and_exact_fnsp_v3(
                    1,
                    &later_commit,
                    &later_notes,
                    1,
                    b"receipt-exact-v3-later",
                    FinalizedFaithfulRootWeld {
                        initial_anchor: None,
                        envelope: &later_envelope,
                        author_committee: std::slice::from_ref(&signer.ed_pk),
                        author_ml_dsa_committee: std::slice::from_ref(&signer.pq_pk),
                        attested_root: &later_attested,
                        spent_nullifiers: std::slice::from_ref(&later_spend),
                        finalized_spends: &later_finalized_spends,
                    },
                    later_exact,
                )
                .unwrap();
            assert!(later_outcome.freshly_committed);
        }

        let reopened = PersistentStore::open(&path).unwrap();
        assert_eq!(reopened.commit_cursor().unwrap(), 2);
        assert_eq!(reopened.note_count().unwrap(), 2);
        assert_eq!(reopened.receipt_chain_len().unwrap(), 2);
        assert_eq!(
            reopened.exact_fnsp_v3_state_head().unwrap(),
            Some(expected_exact_head)
        );
        assert_eq!(
            reopened
                .exact_fnsp_v3_append_records()
                .unwrap()
                .unwrap()
                .len(),
            2
        );
        assert_eq!(
            reopened
                .latest_attested_root()
                .unwrap()
                .unwrap()
                .note_tree_root,
            Some(expected_latest_note_root.to_bytes())
        );
        assert_eq!(
            reopened.load_faithful_nullifier_records().unwrap(),
            vec![
                (dregg_cell::note::Nullifier(spend.nullifier), spend.value, 0),
                (dregg_cell::note::Nullifier([0xc3; 32]), 5_353, 1),
            ]
        );

        let recovered = reopened
            .reconstruct_exact_fnsp_v3_replay_candidate(spend.nullifier, spend.value)
            .unwrap();
        let historical = reopened
            .commit_finalized_turn_with_faithful_root_and_exact_fnsp_v3(
                0,
                &replay_commit,
                &notes,
                0,
                b"receipt-exact-v3",
                FinalizedFaithfulRootWeld {
                    initial_anchor: Some(&replay_anchor),
                    envelope: &replay_envelope,
                    author_committee: std::slice::from_ref(&signer.ed_pk),
                    author_ml_dsa_committee: std::slice::from_ref(&signer.pq_pk),
                    attested_root: &replay_attested,
                    spent_nullifiers: std::slice::from_ref(&spend),
                    finalized_spends: &replay_finalized_spends,
                },
                recovered,
            )
            .unwrap();
        assert!(!historical.freshly_committed);
        assert_eq!(reopened.commit_cursor().unwrap(), 2);
        assert_eq!(reopened.note_count().unwrap(), 2);
        assert_eq!(
            reopened.exact_fnsp_v3_state_head().unwrap(),
            Some(expected_exact_head)
        );
    }

    #[test]
    fn stale_exact_fnsp_v3_cas_aborts_every_earlier_finalized_turn_write() {
        let store = PersistentStore::open_in_memory().unwrap();
        store
            .initialize_exact_fnsp_v3_state_from_faithful_nullifiers()
            .unwrap();
        let signer = FaithfulSigner::new(0x42);
        let block_id = [0xa2; 32];
        let notes = [[0xb2; 32]];
        let spend = FinalizedNullifierRecord {
            nullifier: [0xc2; 32],
            value: 7_777,
        };

        // Prepare the turn's candidate, then let a competing writer advance only the exact
        // authority.  The stale failure happens at the deliberately-last consuming CAS, after
        // every other finalized-turn table mutation has been staged in the same writer.
        let stale = store
            .prepare_exact_fnsp_v3_append(spend.nullifier, spend.value)
            .unwrap();
        let winner = store
            .prepare_exact_fnsp_v3_append([0xd2; 32], 8_888)
            .unwrap();
        let winner_spend = FinalizedNullifierRecord {
            nullifier: [0xd2; 32],
            value: 8_888,
        };
        let winner_head = {
            let write = store.db.begin_write().unwrap();
            append_fresh_nullifiers_in(&write, std::slice::from_ref(&winner_spend), 0).unwrap();
            let (write, head) =
                crate::exact_fnsp_v3_state::compare_and_commit_exact_fnsp_v3_append_in(
                    write, winner,
                )
                .unwrap();
            // The competing writer is a REAL finalized-turn writer, so it also advances the
            // faithful/exact rolling bridge — the O(1) induction boundary every exact commit
            // checks FIRST (`commit_finalized_turn_welded`). Without this the image it leaves is
            // incoherent (bridge 0 / faithful 1 / exact 1) and the commit below is refused by the
            // bridge gate, never reaching the stale-CAS tooth this test exists for.
            crate::exact_fnsp_v3_faithful_bridge::stage_matching_append_in(
                &write,
                winner.append_record(),
                winner.append_record(),
            )
            .unwrap();
            write.commit().unwrap();
            head
        };

        let commit = faithful_commit_record(0, block_id);
        let (anchor, edge) = plan_test_edge(&store, 1, block_id, &notes);
        let envelope = signer.sign_edge(edge.clone());
        let expected_legacy_root = store
            .plan_faithful_nullifier_successor(std::slice::from_ref(&spend))
            .unwrap();
        let attested =
            test_attested_with_nullifier_root(&signer, &commit, &edge, expected_legacy_root);
        let finalized_spends =
            test_finalized_spend_inputs(&store, &anchor, std::slice::from_ref(&spend));

        assert!(matches!(
            store.commit_finalized_turn_with_faithful_root_and_exact_fnsp_v3(
                0,
                &commit,
                &notes,
                0,
                b"must-not-survive",
                FinalizedFaithfulRootWeld {
                    initial_anchor: Some(&anchor),
                    envelope: &envelope,
                    author_committee: std::slice::from_ref(&signer.ed_pk),
                    author_ml_dsa_committee: std::slice::from_ref(&signer.pq_pk),
                    attested_root: &attested,
                    spent_nullifiers: std::slice::from_ref(&spend),
                    finalized_spends: &finalized_spends,
                },
                stale,
            ),
            Err(StoreError::Integrity(ref message)) if message.contains("stale")
        ));

        // The competing exact append remains, while every row staged by the failed carrying
        // transaction is absent.  This is the hostile partial-write/crash boundary assertion.
        assert_eq!(store.exact_fnsp_v3_state_head().unwrap(), Some(winner_head));
        assert_eq!(
            store.exact_fnsp_v3_append_records().unwrap(),
            Some(vec![winner.append_record()])
        );
        assert_eq!(store.commit_cursor().unwrap(), 0);
        assert!(store.commit_record_at(0).unwrap().is_none());
        assert_eq!(store.note_count().unwrap(), 0);
        assert_eq!(store.receipt_chain_len().unwrap(), 0);
        assert!(store.faithful_note_root_head().unwrap().is_none());
        assert!(store.latest_attested_root().unwrap().is_none());
        assert_eq!(
            store.load_faithful_nullifier_records().unwrap(),
            vec![(
                dregg_cell::note::Nullifier(winner_spend.nullifier),
                winner_spend.value,
                0,
            )]
        );
        assert!(
            store
                .finalized_faithful_spend(&spend.nullifier)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn faithful_existing_receipt_weld_never_appends_and_reopens_exactly() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("faithful-existing-receipt.redb");
        let signer = FaithfulSigner::new(0x29);
        let block_id = [0x39; 32];
        let notes = [[0x61; 32], [0x62; 32]];
        let spend = FinalizedNullifierRecord {
            nullifier: [0x63; 32],
            value: 1_337,
        };
        let receipts = [
            b"solo-ingress-receipt".to_vec(),
            b"later-interleaved-receipt".to_vec(),
        ];
        let expected_note_root;
        let expected_nullifier_root;

        {
            let store = PersistentStore::open(&path).unwrap();
            store.append_receipt_chain_entry(0, &receipts[0]).unwrap();
            store.append_receipt_chain_entry(1, &receipts[1]).unwrap();

            let commit = faithful_commit_record(0, block_id);
            let (anchor, edge) = plan_test_edge(&store, 1, block_id, &notes);
            expected_note_root = edge.successor;
            expected_nullifier_root = store.plan_faithful_nullifier_successor(&[spend]).unwrap();
            let envelope = signer.sign_edge(edge.clone());
            let attested =
                test_attested_with_nullifier_root(&signer, &commit, &edge, expected_nullifier_root);
            let finalized_spends = test_finalized_spend_inputs(&store, &anchor, &[spend]);
            let weld = || FinalizedFaithfulRootWeld {
                initial_anchor: Some(&anchor),
                envelope: &envelope,
                author_committee: std::slice::from_ref(&signer.ed_pk),
                author_ml_dsa_committee: std::slice::from_ref(&signer.pq_pk),
                attested_root: &attested,
                spent_nullifiers: std::slice::from_ref(&spend),
                finalized_spends: &finalized_spends,
            };

            // ExistingExact is not an append permission. Even a valid faithful
            // commit must roll back completely when the claimed receipt is the
            // missing dense tail.
            assert!(matches!(
                store.commit_finalized_turn_with_faithful_root_existing_receipt(
                    0,
                    &commit,
                    &notes,
                    2,
                    b"missing-tail-receipt",
                    weld(),
                ),
                Err(StoreError::Integrity(_))
            ));
            assert_eq!(store.commit_cursor().unwrap(), 0);
            assert_eq!(store.note_count().unwrap(), 0);
            assert!(store.load_faithful_nullifier_records().unwrap().is_empty());
            assert!(store.faithful_note_root_head().unwrap().is_none());
            assert!(store.latest_attested_root().unwrap().is_none());
            assert!(store.commit_record_at(0).unwrap().is_none());
            assert_eq!(store.load_receipt_chain().unwrap(), receipts);

            // An older position is immutable: conflicting bytes also abort the
            // whole transaction and leave both dense receipt rows untouched.
            assert!(matches!(
                store.commit_finalized_turn_with_faithful_root_existing_receipt(
                    0,
                    &commit,
                    &notes,
                    0,
                    b"conflicting-receipt",
                    weld(),
                ),
                Err(StoreError::Integrity(_))
            ));
            assert_eq!(store.commit_cursor().unwrap(), 0);
            assert_eq!(store.note_count().unwrap(), 0);
            assert!(store.load_faithful_nullifier_records().unwrap().is_empty());
            assert_eq!(store.load_receipt_chain().unwrap(), receipts);

            // Exact existing receipt zero may carry a later faithful custody
            // commit even though another node-wide receipt is already at the
            // tail. No receipt append or cursor movement occurs.
            let outcome = store
                .commit_finalized_turn_with_faithful_root_existing_receipt(
                    0,
                    &commit,
                    &notes,
                    0,
                    &receipts[0],
                    weld(),
                )
                .unwrap();
            assert!(outcome.freshly_committed);
            assert_eq!(store.commit_cursor().unwrap(), 1);
            assert_eq!(store.note_count().unwrap(), 2);
            assert_eq!(
                store.faithful_nullifier_root().unwrap(),
                expected_nullifier_root
            );
            assert_eq!(store.receipt_chain_len().unwrap(), 2);
            assert_eq!(store.load_receipt_chain().unwrap(), receipts);

            let replay = store
                .commit_finalized_turn_with_faithful_root_existing_receipt(
                    0,
                    &commit,
                    &notes,
                    0,
                    &receipts[0],
                    weld(),
                )
                .unwrap();
            assert!(!replay.freshly_committed);
            assert_eq!(store.note_count().unwrap(), 2);
            assert_eq!(store.load_receipt_chain().unwrap(), receipts);
        }

        let reopened = PersistentStore::open(&path).unwrap();
        assert_eq!(reopened.commit_cursor().unwrap(), 1);
        assert_eq!(reopened.note_count().unwrap(), 2);
        assert_eq!(reopened.receipt_chain_len().unwrap(), 2);
        assert_eq!(reopened.load_receipt_chain().unwrap(), receipts);
        assert_eq!(
            reopened.load_faithful_nullifier_records().unwrap(),
            vec![(dregg_cell::note::Nullifier(spend.nullifier), spend.value, 0)]
        );
        let root = reopened.latest_attested_root().unwrap().unwrap();
        assert_eq!(root.note_tree_root, Some(expected_note_root.to_bytes()));
        assert_eq!(root.nullifier_set_root, Some(expected_nullifier_root));
        assert_eq!(
            reopened.faithful_note_root_head().unwrap().unwrap().root,
            expected_note_root
        );
    }

    #[test]
    fn faithful_root_weld_refuses_fork_without_partial_commit() {
        let store = PersistentStore::open_in_memory().unwrap();
        let signer = FaithfulSigner::new(0x22);
        let first_block = [0x32; 32];
        let first_commit = faithful_commit_record(0, first_block);
        let (anchor, first_edge) = plan_test_edge(&store, 1, first_block, &[[0x43; 32]]);
        let first_envelope = signer.sign_edge(first_edge.clone());
        let first_attested = test_attested(&signer, &first_commit, &first_edge);
        store
            .commit_finalized_turn_with_faithful_root(
                0,
                &first_commit,
                &[[0x43; 32]],
                0,
                b"receipt-0",
                FinalizedFaithfulRootWeld {
                    initial_anchor: Some(&anchor),
                    envelope: &first_envelope,
                    author_committee: &[signer.ed_pk],
                    author_ml_dsa_committee: std::slice::from_ref(&signer.pq_pk),
                    attested_root: &first_attested,
                    spent_nullifiers: &[],
                    finalized_spends: &[],
                },
            )
            .unwrap();

        let second_block = [0x33; 32];
        let second_commit = faithful_commit_record(1, second_block);
        let (_, mut sibling) = plan_test_edge(&store, 2, second_block, &[[0x44; 32]]);
        sibling.predecessor = anchor.root; // authenticated sibling of the consumed head
        let sibling_envelope = signer.sign_edge(sibling.clone());
        let sibling_attested = test_attested(&signer, &second_commit, &sibling);
        assert!(
            store
                .commit_finalized_turn_with_faithful_root(
                    1,
                    &second_commit,
                    &[[0x44; 32]],
                    1,
                    b"receipt-1",
                    FinalizedFaithfulRootWeld {
                        initial_anchor: None,
                        envelope: &sibling_envelope,
                        author_committee: &[signer.ed_pk],
                        author_ml_dsa_committee: std::slice::from_ref(&signer.pq_pk),
                        attested_root: &sibling_attested,
                        spent_nullifiers: &[],
                        finalized_spends: &[],
                    },
                )
                .is_err()
        );
        assert_eq!(store.commit_cursor().unwrap(), 1);
        assert_eq!(store.note_count().unwrap(), 1);
        assert!(store.attested_root_at_height(2).unwrap().is_none());
        assert_eq!(store.faithful_note_root_head().unwrap().unwrap().height, 1);
    }

    #[test]
    fn faithful_root_history_truncation_refuses_after_restart() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("faithful-truncated.redb");
        let signer = FaithfulSigner::new(0x23);
        let block_id = [0x34; 32];
        let expected;
        {
            let store = PersistentStore::open(&path).unwrap();
            let commit = faithful_commit_record(0, block_id);
            let (anchor, edge) = plan_test_edge(&store, 1, block_id, &[[0x45; 32]]);
            expected = crate::FaithfulNoteRootExpectationV1 {
                records: 1,
                height: 1,
                note_count: 1,
                root: edge.successor,
            };
            let envelope = signer.sign_edge(edge.clone());
            let attested = test_attested(&signer, &commit, &edge);
            store
                .commit_finalized_turn_with_faithful_root(
                    0,
                    &commit,
                    &[[0x45; 32]],
                    0,
                    b"receipt-0",
                    FinalizedFaithfulRootWeld {
                        initial_anchor: Some(&anchor),
                        envelope: &envelope,
                        author_committee: &[signer.ed_pk],
                        author_ml_dsa_committee: std::slice::from_ref(&signer.pq_pk),
                        attested_root: &attested,
                        spent_nullifiers: &[],
                        finalized_spends: &[],
                    },
                )
                .unwrap();
            let write = store.db.begin_write().unwrap();
            {
                let mut history = write
                    .open_table(tables::FAITHFUL_NOTE_ROOT_HISTORY)
                    .unwrap();
                history.remove(1).unwrap();
            }
            write.commit().unwrap();
        }

        let reopened = PersistentStore::open(&path).unwrap();
        assert!(
            reopened
                .load_faithful_note_root_history_hybrid(
                    &[signer.ed_pk],
                    std::slice::from_ref(&signer.pq_pk),
                    1,
                    expected,
                )
                .is_err(),
            "a deleted tail with a surviving seal must not restart as a valid prefix"
        );
        assert!(reopened.faithful_note_root_head().is_err());
    }

    #[test]
    fn faithful_root_weld_rejects_legacy_scalar_x_plus_p_alias() {
        let store = PersistentStore::open_in_memory().unwrap();
        let signer = FaithfulSigner::new(0x24);
        let block_id = [0x35; 32];
        let x = 1_000_000u32;
        let x_plus_p = x + dregg_circuit::field::BABYBEAR_P;
        let mut honest = [0u8; 32];
        let mut alias = [0u8; 32];
        honest[..4].copy_from_slice(&x.to_le_bytes());
        alias[..4].copy_from_slice(&x_plus_p.to_le_bytes());
        assert_eq!(
            dregg_commit::poseidon2_tree::commitment_to_field(&honest),
            dregg_commit::poseidon2_tree::commitment_to_field(&alias),
            "the hostile fixture must alias under the retired one-felt bridge"
        );

        let commit = faithful_commit_record(0, block_id);
        let (anchor, _) = plan_test_edge(&store, 1, block_id, &[honest]);
        let alias_tree = Poseidon2NoteTree::with_depth(LIVE_NOTE_TREE_DEPTH);
        let alias_edge =
            crate::plan_faithful_note_root_transition_v1(&alias_tree, &anchor, block_id, &[alias])
                .unwrap();
        let alias_envelope = signer.sign_edge(alias_edge.clone());
        let alias_attested = test_attested(&signer, &commit, &alias_edge);
        assert!(
            store
                .commit_finalized_turn_with_faithful_root(
                    0,
                    &commit,
                    &[honest],
                    0,
                    b"receipt-0",
                    FinalizedFaithfulRootWeld {
                        initial_anchor: Some(&anchor),
                        envelope: &alias_envelope,
                        author_committee: &[signer.ed_pk],
                        author_ml_dsa_committee: std::slice::from_ref(&signer.pq_pk),
                        attested_root: &alias_attested,
                        spent_nullifiers: &[],
                        finalized_spends: &[],
                    },
                )
                .is_err(),
            "a legacy scalar alias must not substitute for the exact faithful root"
        );
        assert_eq!(store.commit_cursor().unwrap(), 0);
        assert_eq!(store.note_count().unwrap(), 0);
        assert!(store.latest_attested_root().unwrap().is_none());
    }

    #[test]
    fn faithful_root_weld_atomically_persists_nullifier_tail_and_exact_replay() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("faithful-nullifiers.redb");
        let signer = FaithfulSigner::new(0x25);
        let spends = [
            FinalizedNullifierRecord {
                nullifier: [0x51; 32],
                value: 700,
            },
            FinalizedNullifierRecord {
                nullifier: [0x52; 32],
                value: 900,
            },
        ];
        let expected_root;

        {
            let store = PersistentStore::open(&path).unwrap();
            expected_root = store.plan_faithful_nullifier_successor(&spends).unwrap();
            let block_id = [0x36; 32];
            let commit = faithful_commit_record(0, block_id);
            let (anchor, edge) = plan_test_edge(&store, 1, block_id, &[]);
            let envelope = signer.sign_edge(edge.clone());
            let attested =
                test_attested_with_nullifier_root(&signer, &commit, &edge, expected_root);
            let finalized_spends = test_finalized_spend_inputs(&store, &anchor, &spends);
            let weld = || FinalizedFaithfulRootWeld {
                initial_anchor: Some(&anchor),
                envelope: &envelope,
                author_committee: std::slice::from_ref(&signer.ed_pk),
                author_ml_dsa_committee: std::slice::from_ref(&signer.pq_pk),
                attested_root: &attested,
                spent_nullifiers: &spends,
                finalized_spends: &finalized_spends,
            };

            let outcome = store
                .commit_finalized_turn_with_faithful_root(
                    0,
                    &commit,
                    &[],
                    0,
                    b"receipt-nullifiers",
                    weld(),
                )
                .unwrap();
            assert!(outcome.freshly_committed);
            assert_eq!(store.faithful_nullifier_root().unwrap(), expected_root);
            assert_eq!(
                store.load_faithful_nullifier_records().unwrap(),
                vec![
                    (dregg_cell::note::Nullifier([0x51; 32]), 700, 0),
                    (dregg_cell::note::Nullifier([0x52; 32]), 900, 1),
                ]
            );
            let authorities = store
                .finalized_faithful_spends_for_turn(&commit.turn_hash)
                .unwrap();
            assert_eq!(authorities.len(), 2);
            for (index, authority) in authorities.iter().enumerate() {
                assert_eq!(authority.turn_hash(), commit.turn_hash);
                assert_eq!(authority.turn_receipt_hash(), commit.receipt_hash);
                assert_eq!(authority.spend_agent(), commit.creator);
                assert_eq!(authority.spend_index(), u32::try_from(index).unwrap());
                assert_eq!(authority.root_height(), anchor.height);
                assert_eq!(authority.historical_note_root8(), anchor.root.to_bytes());
                assert_eq!(authority.nullifier(), spends[index].nullifier);
                assert_eq!(authority.value(), spends[index].value);
                assert_eq!(authority.asset_type(), 0x7000 + index as u64);
                assert_eq!(
                    authority.successor_nullifier_root8(),
                    finalized_spends[index].successor_nullifier_root.to_bytes()
                );
                assert_eq!(authority.finalized_height(), commit.height);
                assert_eq!(authority.block_id(), commit.block_id);
                assert_eq!(authority.federation_id(), edge.federation_id);
                assert_eq!(authority.finality_round(), Some(commit.height));
                assert_ne!(authority.attested_root_digest(), [0; 32]);
                assert_ne!(authority.authority_digest(), [0; 32]);
            }
            assert_eq!(
                store
                    .finalized_faithful_spend(&spends[1].nullifier)
                    .unwrap()
                    .unwrap(),
                authorities[1]
            );

            let replay = store
                .commit_finalized_turn_with_faithful_root(
                    0,
                    &commit,
                    &[],
                    0,
                    b"receipt-nullifiers",
                    weld(),
                )
                .unwrap();
            assert!(!replay.freshly_committed);

            let mut conflicting_statement = finalized_spends.clone();
            conflicting_statement[1].asset_type ^= 1;
            assert!(
                store
                    .commit_finalized_turn_with_faithful_root(
                        0,
                        &commit,
                        &[],
                        0,
                        b"receipt-nullifiers",
                        FinalizedFaithfulRootWeld {
                            finalized_spends: &conflicting_statement,
                            ..weld()
                        },
                    )
                    .is_err(),
                "an exact replay cannot substitute a different public asset type"
            );

            let conflicting = [
                spends[0],
                FinalizedNullifierRecord {
                    nullifier: spends[1].nullifier,
                    value: spends[1].value + 1,
                },
            ];
            assert!(
                store
                    .commit_finalized_turn_with_faithful_root(
                        0,
                        &commit,
                        &[],
                        0,
                        b"receipt-nullifiers",
                        FinalizedFaithfulRootWeld {
                            spent_nullifiers: &conflicting,
                            ..weld()
                        },
                    )
                    .is_err(),
                "an exact replay cannot substitute a different public note value"
            );
            assert_eq!(store.commit_cursor().unwrap(), 1);
        }

        let reopened = PersistentStore::open(&path).unwrap();
        assert_eq!(reopened.faithful_nullifier_root().unwrap(), expected_root);
        assert_eq!(reopened.commit_cursor().unwrap(), 1);
        assert_eq!(
            reopened
                .finalized_faithful_spends_for_turn(
                    &faithful_commit_record(0, [0x36; 32]).turn_hash
                )
                .unwrap()
                .len(),
            2,
            "store-minted spend authorities survive restart"
        );
    }

    #[test]
    fn faithful_root_weld_refuses_duplicate_or_wrong_nullifier_root_without_partial_commit() {
        let store = PersistentStore::open_in_memory().unwrap();
        let signer = FaithfulSigner::new(0x26);
        let block_id = [0x37; 32];
        let commit = faithful_commit_record(0, block_id);
        let (anchor, edge) = plan_test_edge(&store, 1, block_id, &[[0x53; 32]]);
        let envelope = signer.sign_edge(edge.clone());
        let duplicate = FinalizedNullifierRecord {
            nullifier: [0x54; 32],
            value: 111,
        };
        let attested = test_attested(&signer, &commit, &edge);
        assert!(
            store
                .commit_finalized_turn_with_faithful_root(
                    0,
                    &commit,
                    &[[0x53; 32]],
                    0,
                    b"receipt-duplicate",
                    FinalizedFaithfulRootWeld {
                        initial_anchor: Some(&anchor),
                        envelope: &envelope,
                        author_committee: std::slice::from_ref(&signer.ed_pk),
                        author_ml_dsa_committee: std::slice::from_ref(&signer.pq_pk),
                        attested_root: &attested,
                        spent_nullifiers: &[duplicate, duplicate],
                        finalized_spends: &[],
                    },
                )
                .is_err(),
            "a within-turn duplicate must refuse before any durable write"
        );
        assert_eq!(store.commit_cursor().unwrap(), 0);
        assert_eq!(store.note_count().unwrap(), 0);
        assert!(store.load_faithful_nullifier_records().unwrap().is_empty());
        assert!(store.latest_attested_root().unwrap().is_none());

        let one = [duplicate];
        let true_root = store.plan_faithful_nullifier_successor(&one).unwrap();
        let finalized_spends = test_finalized_spend_inputs(&store, &anchor, &one);
        assert_ne!(attested.nullifier_set_root, Some(true_root));
        assert!(
            store
                .commit_finalized_turn_with_faithful_root(
                    0,
                    &commit,
                    &[[0x53; 32]],
                    0,
                    b"receipt-wrong-root",
                    FinalizedFaithfulRootWeld {
                        initial_anchor: Some(&anchor),
                        envelope: &envelope,
                        author_committee: std::slice::from_ref(&signer.ed_pk),
                        author_ml_dsa_committee: std::slice::from_ref(&signer.pq_pk),
                        attested_root: &attested,
                        spent_nullifiers: &one,
                        finalized_spends: &finalized_spends,
                    },
                )
                .is_err(),
            "an attestation over the predecessor root must not authorize a spend"
        );
        assert_eq!(store.commit_cursor().unwrap(), 0);
        assert_eq!(store.note_count().unwrap(), 0);
        assert!(store.load_faithful_nullifier_records().unwrap().is_empty());
    }

    #[test]
    fn faithful_nullifier_record_truncation_refuses_after_restart() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("faithful-nullifier-truncated.redb");
        let signer = FaithfulSigner::new(0x27);
        let spend = FinalizedNullifierRecord {
            nullifier: [0x55; 32],
            value: 31337,
        };
        {
            let store = PersistentStore::open(&path).unwrap();
            let block_id = [0x38; 32];
            let commit = faithful_commit_record(0, block_id);
            let (anchor, edge) = plan_test_edge(&store, 1, block_id, &[]);
            let envelope = signer.sign_edge(edge.clone());
            let expected = store.plan_faithful_nullifier_successor(&[spend]).unwrap();
            let attested = test_attested_with_nullifier_root(&signer, &commit, &edge, expected);
            let finalized_spends = test_finalized_spend_inputs(&store, &anchor, &[spend]);
            store
                .commit_finalized_turn_with_faithful_root(
                    0,
                    &commit,
                    &[],
                    0,
                    b"receipt-truncated-nullifier",
                    FinalizedFaithfulRootWeld {
                        initial_anchor: Some(&anchor),
                        envelope: &envelope,
                        author_committee: std::slice::from_ref(&signer.ed_pk),
                        author_ml_dsa_committee: std::slice::from_ref(&signer.pq_pk),
                        attested_root: &attested,
                        spent_nullifiers: &[spend],
                        finalized_spends: &finalized_spends,
                    },
                )
                .unwrap();
            let write = store.db.begin_write().unwrap();
            {
                let mut records = write.open_table(tables::NULLIFIER_RECORDS_V1).unwrap();
                records.remove(&spend.nullifier).unwrap();
            }
            write.commit().unwrap();
        }

        let reopened = PersistentStore::open(&path).unwrap();
        assert!(reopened.faithful_nullifier_root().is_err());
        assert!(
            reopened.plan_faithful_nullifier_successor(&[]).is_err(),
            "a truncated accumulator must not be silently accepted as a prefix"
        );
    }
}
