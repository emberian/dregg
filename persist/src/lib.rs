//! `dregg-persist`: the node's ONE durable store (.docs-history-noclaude/PERSISTENCE.md).
//!
//! This crate provides the node's durable storage — the commit log + index,
//! ledger checkpoints, blocklace blocks/meta, notes/nullifiers, attested
//! roots, forever-digest sets, channel rosters, and config blobs — backed by
//! `redb` (embedded ACID, WAL): every durable write is a transaction that
//! either commits fully (fsync at the commit boundary) or not at all.
//!
//! The [`commit_log`] module is the recovery spine: each applied turn's
//! durable record, the commit cursor advance, and every index entry
//! (receipt-by-hash, turn-by-hash, turn-by-(height, creator, ordinal),
//! cell-by-id) are written in ONE redb transaction, so recovery converges to
//! a consistent checkpoint with no torn state, no lost finalized turn, and no
//! double-apply. The index is rebuildable from — and provably agrees with —
//! the log (`verify_index_agrees_with_log`). A turn that burns anti-replay
//! digests can land them in the SAME transaction
//! (`commit_finalized_turn_with_burns` — the same-transaction burn weld).
//!
//! ## dregg1 residue, retired
//!
//! The `tokens` (TokenChain/fold steps), `recovery`
//! (`recover_federation_state`), `keys` (encrypted signing keys; the node
//! keeps its key in `node.key`) and `audit` (standalone audit log) modules
//! were dregg1-era residue with zero consumers outside this crate's own
//! tests; they were deleted under the cutover-ledger discipline (verified
//! zero external consumers by grep at deletion time). Their tables are no
//! longer created; pre-existing tables in an old store file are simply
//! ignored by redb.

pub mod blocklace_store;
pub mod channel_rosters;
pub mod checkpoint;
pub mod commit_log;
mod exact_fnsp_v3_faithful_bridge;
pub mod exact_fnsp_v3_frame_head;
pub mod exact_fnsp_v3_state;
pub mod executor_consensus_state;
pub mod faithful_note_root_history;
pub mod federation;
pub mod finalized_faithful_spend;
pub mod finalized_receipt_core_v1;
pub mod forever_digests;
pub mod image_builder;
pub mod ledger_store;
pub mod note_tree;
pub mod per_cell_receipt_heads;
pub mod poa_activated_content;
pub mod poa_authority_export;
mod poa_compact_authority;
pub mod poa_event_batch_plan;
pub mod poa_event_batch_v2;
pub mod poa_event_store;
pub mod poa_galley_authority;
pub mod poa_holding_consumption;
pub mod poa_signal_session;
pub mod poa_signal_slot;
pub mod poa_signal_state;
pub mod poa_world_activation;
pub mod poseidon2_note_tree;
pub mod private_dependent_turns;
pub mod promise_resolutions;
pub mod snapshot;
pub mod tables;

#[cfg(test)]
mod tests;

use std::path::Path;

use redb::{Database, ReadableTable, ReadableTableMetadata};

pub use blocklace_store::BlocklaceMeta;
pub use commit_log::{
    CellOverlayOp, CommitRecord, ExactFnspV3FrameCommitOutcome, FinalizedNullifierRecord,
    IndexAuditReport,
};
pub use exact_fnsp_v3_frame_head::{
    CommittedExactFnspV3FrameHeadV1, EXACT_FNSP_V3_ACTIVATION_V1_WIRE_LEN,
    EXACT_FNSP_V3_FRAME_V1_WIRE_LEN, ExactFnspV3DurableReceiptLinkV1, ExactFnspV3FrameStoreError,
    StoreAuthenticatedExactFnspV3ActivationV1, UntrustedExactFnspV3ActivationV1,
    UntrustedExactFnspV3FrameV1,
};
pub use exact_fnsp_v3_state::{
    EXACT_FNSP_V3_APPEND_RECORD_V1_WIRE_LEN, EXACT_FNSP_V3_STATE_HEAD_V1_WIRE_LEN,
    ExactFnspV3StateCasV1, ExactFnspV3StateHeadV1, ExactFnspV3StateStoreError,
    PreparedExactFnspV3StateTransitionV1,
};
pub use executor_consensus_state::{
    ExecutorAccumulatorSnapshot, ExecutorNoteCommitmentRecord, ExecutorRevocationRecord,
    FinalizedExecutorConsensusState, ReactiveNullifierCasV1, ReactiveRegistryCasV1,
    reactive_nullifier_commitment, reactive_registry_commitment,
};
pub use faithful_note_root_history::{
    AuthenticatedFaithfulNoteRootPrefix, CanonicalFaithfulRoot, FaithfulNoteRootAnchorV1,
    FaithfulNoteRootAuditSealV1, FaithfulNoteRootEnvelopeV1,
    FaithfulNoteRootExpectationV1, FaithfulNoteRootHistoryError, FaithfulNoteRootHistoryV1,
    FaithfulNoteRootRecordV1, plan_faithful_note_root_transition_v1,
};
pub use federation::{QuorumSignature, StoredAttestedRoot, hybrid_quorum_from_finalization_quorum};
pub use finalized_faithful_spend::{FinalizedFaithfulSpend, FinalizedFaithfulSpendInput};
pub use finalized_receipt_core_v1::DurableFinalizedReceiptCoreHeadV1;
pub use image_builder::{
    BuildError, CellSpec, ImageArtifact, ImageAttestation, ImageFacts, ImageManifest, VerifyError,
    build_image, verify_image,
};
pub use ledger_store::LedgerCheckpoint;
pub use note_tree::{NoteTree, PersistentNullifierSet};
pub use per_cell_receipt_heads::{
    DurablePerCellReceiptHead, MAX_PER_CELL_RECEIPT_HEADS_V1, MAX_PER_CELL_RECEIPT_LIVE_RECORDS_V1,
    PER_CELL_RECEIPT_HEAD_INDEX_VERSION_V1, PerCellReceiptHeadRecovery,
};
pub use poa_activated_content::{
    PoaActivatedContentInstallOutcomeV1, PoaActivatedContentInstallStatusV1,
};
pub use poa_authority_export::PoaAuthorityCommitSnapshotV1;
pub use poa_compact_authority::{
    FinalizedCommitAuthorityV1, PoaCompactCheckpointStatementV1, PoaCompactTrustPolicyV1,
    PoaCompactTrustRootV1, SignedPoaCompactCheckpointAnchorV1,
};
pub use poa_event_batch_plan::{
    PoaEventBatchInitialHeadOriginV2, PoaEventBatchPlanAuthorityV2,
    PoaEventBatchPlanEventAuthorityV2, PoaEventBatchPlanInitialHeadV2,
    prepare_poa_event_batch_v2_from_lean_plan,
};
pub use poa_event_batch_v2::{
    FinalizedTurnCoordinateV2, MAX_POA_BATCH_COMPONENT_BYTES_V2, MAX_POA_BATCH_EVENTS_V2,
    MAX_POA_BATCH_FRAME_BYTES_V2, PoaBatchStreamHeadV2, PoaBatchStreamIdV2, PoaEventBatchHistoryV2,
    PoaRecordedBatchEventV2, PoaWorldIdentityV2, PreparedPoaBatchEventV2, PreparedPoaEventBatchV2,
};
pub use poa_event_store::{
    MAX_POA_EVENT_COMPONENT_BYTES_V1, MAX_POA_EVENT_TAG_BYTES_V1, PoaAggregateIdV1,
    PoaEventEnvelopeV1, PoaEventHeadV1, PoaEventHistoryV1, PoaProjectionCursorV1,
    PreparedPoaEventEnvelopeV1,
};
pub use poa_galley_authority::{
    AuthenticatedPoaGalleyPolicyV1, PreparedPoaFinalizedTurnAuthorityV1,
    PreparedPoaGalleyEventBatchV1,
};
pub use poa_holding_consumption::{PoaHoldingConsumptionV1, PreparedPoaHoldingConsumptionV1};
pub use poa_signal_session::{
    POA_SIGNAL_SESSION_MAX_ROUNDS, POA_SIGNAL_SESSION_SCHEMA_V1, PoaSignalSessionRefusalV1,
    PoaSignalSessionRoundV1, PoaSignalSessionV1,
};
pub use poa_signal_slot::{
    POA_SLOT_OPENING_STATEMENT_SCHEMA_V1, PoaInstalledSlotV1, PoaSlotInstallStatusV1,
    PoaSlotOpeningStatementV1, PoaSlotRevealStatusV1, PoaSlotRevealV1,
    SignedPoaSlotOpeningEnvelopeV1,
};
pub use poa_signal_state::{
    MAX_POA_SIGNAL_WIRE_BYTES_V1, PoaSignalGenesisInitOutcome, PoaSignalHeadV1,
    PoaSignalTransitionV1, PreparedPoaSignalTransitionV1,
};
pub use poa_world_activation::{
    PoaActiveWorldHeadV1, PoaWorldActivationKindV1, PoaWorldActivationRecordV1,
    PoaWorldActivationStatementV1, PreparedPoaWorldActivationV1,
    SignedPoaWorldActivationEnvelopeV1,
};
pub use poseidon2_note_tree::Poseidon2NoteTree;
pub use private_dependent_turns::{
    ClaimedPrivateDependentTurnV1, PrivateDependentIngressReservationSnapshotV1,
    PrivateDependentIngressReservationStatusV1, PrivateDependentTurnFinishV1,
    PrivateDependentTurnSnapshotV1, PrivateDependentTurnStatusV1,
    private_dependent_ingress_reservation_id_v1, private_dependent_ready_digest_v1,
};
pub use promise_resolutions::{
    DurablePromiseResolutionV1, PromiseBrokenReasonV1, PromiseResolutionCandidateV1,
    PromiseResolutionKindV1,
};
pub use snapshot::{Snapshot, SnapshotHead};

/// THE canonical ledger root — the byte-pinned full-ledger commitment both the
/// node (attested-root convergence across the quorum) and the single-image World
/// (durable-reopen convergence) check against. This is the ONE shared
/// implementation, lifted here so callers stop duplicating it (it was the node's
/// `pub(crate)` copy in `blocklace_sync.rs` + a byte-for-byte replica in
/// `starbridge-v2/src/persistence.rs`; the M4 "shared pub fn lift" tail).
///
/// `BLAKE3-derive-key("dregg-ledger-root-v3")` over the cells sorted by id,
/// length-prefixed, each leaf `BLAKE3(postcard(WHOLE cell))` — committing the whole
/// cell (public_key / token_id / capabilities / lifecycle / state), so two ledgers
/// that finalized the same turns but ended with divergent cell CONTENT (not just
/// balance/nonce) produce DIFFERENT roots — the divergence is loud, not silent.
///
/// Byte-stability is load-bearing (a persisted/attested root must reproduce
/// exactly), so the construction (domain key, sort order, length prefix, whole-cell
/// postcard leaves) is fixed; do not alter it without a domain bump.
pub fn canonical_ledger_root(ledger: &dregg_cell::Ledger) -> [u8; 32] {
    canonical_ledger_root_from_leaves(&canonical_ledger_leaves(ledger))
}

/// The sorted leaf set underlying [`canonical_ledger_root`]: `(cell_id,
/// BLAKE3(postcard(cell)))` for every cell, sorted by id. Exposed so an
/// inclusion-proof endpoint can hand a verifier the FULL leaf set to recompute the
/// root from (the flat root has no O(log n) opening). The construction MUST stay
/// byte-identical to `canonical_ledger_root` — both fold through
/// [`canonical_ledger_root_from_leaves`].
pub fn canonical_ledger_leaves(ledger: &dregg_cell::Ledger) -> Vec<([u8; 32], [u8; 32])> {
    let mut entries: Vec<([u8; 32], [u8; 32])> = ledger
        .iter()
        .map(|(id, cell)| (*id.as_bytes(), canonical_ledger_leaf(cell)))
        .collect();
    entries.sort_by_key(|a| a.0);
    entries
}

/// ONE cell's canonical leaf — `BLAKE3(postcard(WHOLE cell))`, the value
/// [`canonical_ledger_leaves`] pairs with the cell's id.
///
/// Exposed so a caller that maintains an INCREMENTAL leaf set (the single-image
/// World's durable commit — `starbridge_v2::persistence`, which re-derives only
/// the turn's touched cells instead of the whole ledger) computes the leaf with
/// THIS function rather than a byte-for-byte replica of it. The replica is the
/// hazard: two copies that agree today are two copies that disagree after the
/// next `Cell` field lands, and the disagreement surfaces as an unopenable
/// image. There is exactly one leaf construction and it is here.
pub fn canonical_ledger_leaf(cell: &dregg_cell::Cell) -> [u8; 32] {
    let bytes = postcard::to_stdvec(cell).unwrap_or_default();
    *blake3::hash(&bytes).as_bytes()
}

/// Fold the domain-separated flat root over an ALREADY-SORTED leaf set. Callers that
/// already hold the leaves (an inclusion-proof verifier) reuse this instead of
/// re-hashing cells; the fold order (len prefix, then id then leaf-hash per entry)
/// is fixed and load-bearing.
pub fn canonical_ledger_root_from_leaves(entries: &[([u8; 32], [u8; 32])]) -> [u8; 32] {
    canonical_ledger_root_from_sorted(entries.len(), entries.iter().map(|(id, h)| (id, h)))
}

/// The allocation-free twin of [`canonical_ledger_root_from_leaves`]: fold the
/// canonical root over an ALREADY-SORTED `(id, leaf)` iterator of known length.
///
/// A caller holding its leaves in a `BTreeMap<[u8;32], [u8;32]>` (sorted by id by
/// construction — the same `Ord` the `sort_by_key` above uses) folds straight out
/// of the map with no intermediate `Vec`. Both entry points go through THIS fold,
/// so the byte-pinned order (u64 length prefix, then id then leaf-hash per entry)
/// has one implementation.
pub fn canonical_ledger_root_from_sorted<'a>(
    len: usize,
    entries: impl Iterator<Item = (&'a [u8; 32], &'a [u8; 32])>,
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-ledger-root-v3");
    hasher.update(&(len as u64).to_le_bytes());
    for (id, h) in entries {
        hasher.update(id);
        hasher.update(h);
    }
    *hasher.finalize().as_bytes()
}

/// Errors that can occur during store operations.
#[derive(Debug)]
pub enum StoreError {
    /// The underlying database returned an error.
    Database(String),
    /// Serialization/deserialization failure.
    Serialization(String),
    /// Encryption or decryption failure.
    Crypto(String),
    /// The requested item was not found.
    NotFound,
    /// Data integrity check failed.
    Integrity(String),
    /// The durable commit log is corrupt INSIDE its committed prefix: the
    /// reconstruction through `ordinal` does not reach that record's recorded
    /// `ledger_root`, yet a LATER record (`converged_at`) does. That is not a
    /// torn tail — a crash tears a suffix, never a middle — so there is nothing
    /// to truncate to, and the image is refused (F3). Before 2026-09-30 the
    /// torn-tail walk evaluated every ordinal, remembered only the last match,
    /// and opened the image as clean whenever the head converged.
    IntermediateRootMismatch {
        /// The first commit ordinal whose recorded root the reconstruction misses.
        ordinal: u64,
        /// That record's finalized height.
        height: u64,
        /// The later ordinal whose recorded root the reconstruction DOES reach.
        converged_at: u64,
    },
}

impl std::fmt::Display for StoreError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Database(msg) => write!(f, "database error: {msg}"),
            Self::Serialization(msg) => write!(f, "serialization error: {msg}"),
            Self::Crypto(msg) => write!(f, "crypto error: {msg}"),
            Self::NotFound => write!(f, "not found"),
            Self::Integrity(msg) => write!(f, "integrity error: {msg}"),
            Self::IntermediateRootMismatch {
                ordinal,
                height,
                converged_at,
            } => write!(
                f,
                "commit-log intermediate root mismatch: record at ordinal {ordinal} (height \
                 {height}) does not reconstruct to its recorded ledger_root, while ordinal \
                 {converged_at} after it does — corruption inside the committed prefix, not a \
                 torn tail; refusing the image"
            ),
        }
    }
}

impl std::error::Error for StoreError {}

impl From<redb::DatabaseError> for StoreError {
    fn from(e: redb::DatabaseError) -> Self {
        Self::Database(e.to_string())
    }
}

impl From<redb::TableError> for StoreError {
    fn from(e: redb::TableError) -> Self {
        Self::Database(e.to_string())
    }
}

impl From<redb::TransactionError> for StoreError {
    fn from(e: redb::TransactionError) -> Self {
        Self::Database(e.to_string())
    }
}

impl From<redb::CommitError> for StoreError {
    fn from(e: redb::CommitError) -> Self {
        Self::Database(e.to_string())
    }
}

impl From<redb::StorageError> for StoreError {
    fn from(e: redb::StorageError) -> Self {
        Self::Database(e.to_string())
    }
}

impl From<postcard::Error> for StoreError {
    fn from(e: postcard::Error) -> Self {
        Self::Serialization(e.to_string())
    }
}

/// Result type alias for store operations.
pub type Result<T> = std::result::Result<T, StoreError>;

#[cfg(test)]
thread_local! {
    // Consumed by one batch on this test thread. Returning before commit drops
    // the real redb transaction, so tests can observe rollback of an inserted row.
    static FAIL_CONFIG_BATCH_AFTER: std::cell::Cell<Option<usize>> = const {
        std::cell::Cell::new(None)
    };
}

/// The persistent store for all dregg state.
///
/// Backed by `redb`, an embedded ACID key-value store. All operations are
/// crash-safe through redb's write-ahead logging.
pub struct PersistentStore {
    db: Database,
    /// Test-only fault seam for [`Self::persist_block`]. When set, `persist_block`
    /// returns a database error instead of writing, so a node durability test can
    /// drive the authored-block fail-closed/rollback path (finding F2) through the
    /// REAL producer (`submit_heartbeat` / `produce_round_block`). Always compiled
    /// — one relaxed atomic load per block persist — and NEVER set in production.
    fail_persist_block: std::sync::atomic::AtomicBool,
    /// Test-only fault seam for [`Self::get_config`] / [`Self::set_config`]. When
    /// set, both return a database error instead of touching redb, so a caller's
    /// fail-CLOSED disposition on an unreadable/unwritable config key can be shown
    /// to FIRE. Written for `/api/discharge`, whose replay set lives under a config
    /// key: an unreadable one used to yield an EMPTY replay set (every prior ticket
    /// replayable) and an unwritable one used to warn and still answer
    /// `success: true`. Always compiled — one relaxed atomic load per config
    /// operation — and NEVER set in production.
    fail_config_io: std::sync::atomic::AtomicBool,
    /// Incremental cache for [`Self::per_cell_receipt_heads_v1`].
    per_cell_head_cache: per_cell_receipt_heads::PerCellReceiptHeadCache,
}

impl PersistentStore {
    /// Canonical-state re-genesis epoch installed in [`tables::METADATA`].
    /// Epoch 11 pairs the exact fields-root leaf with ledger-root v3.
    ///
    /// Epoch 12 splits `Cell.token_id` into a NAME SALT plus a separate
    /// [`dregg_cell::Cell::asset`] (the currency the cell's balance is
    /// denominated in). `asset` is a trailing serialized field and postcard is
    /// positional, so a pre-v12 `LedgerCheckpoint` cannot be decoded — the gate
    /// below refuses such a store outright ("re-genesis is required") rather
    /// than reinterpreting it. That refusal IS the migration: no live ledger
    /// carries value on this tree (the devnet was decommissioned 2026-06-22 and
    /// no `*.redb` is tracked in git), so the correct answer for an existing
    /// store is to re-genesis it, exactly as the v10→v11 fields-root change did.
    ///
    /// Epoch 13 changed what `fields[0..7]` COMMIT TO: `field_limbs8` lanes 2..7 stopped being six
    /// `u32 % p` chunks over `0..24` — an encoding that collided in `O(1)` on the only octet in the
    /// rotated commitment with no byte-exact companion — and became a Poseidon2 image over an
    /// injective 16 × u16-LE preimage of the whole 32-byte value.
    ///
    /// **Epoch 14 changes it AGAIN, and this time to an INJECTION.** Epoch 13 was a containment, not
    /// a fix: eight BabyBear lanes carry `8 · log₂ p = 247.26` bits against a 32-byte field's 256, so
    /// no 8-lane encoding of 32 bytes is injective under ANY chunking — pigeonhole, whatever the
    /// lanes contain. Its honest price was a **2^92.7 COLLISION** (the birthday bound over the six
    /// image lanes; lanes 0/1 are `u32 % p` and an attacker matches them for free), which is BELOW
    /// this tree's own ~124-bit bar and made the fields octet the weakest collision term in the
    /// rotated commitment. It was written up at the time as "~2^185" — the *second-preimage* figure
    /// for the same object, which is how a below-bar result read as a win.
    ///
    /// The producers (`turn::rotation_witness::produce`,
    /// `dregg_cell::commitment::compute_rotated_pre_limbs`) now write
    /// `Faithful9::from_field_lanes9` over the nine-lane `effect_vm::field_limbs9`, whose Lean
    /// authority `Dregg2.Circuit.FieldLanes9` carries `fieldToLanes9_injective` — proved from a total
    /// decoder and a machine-checked left inverse, `#assert_axioms`-clean — plus
    /// `nine_lanes_is_the_minimum` (`P^8 < 2^256 ≤ P^9`). `field_limbs8`,
    /// `Faithful8::from_field_limbs8` and `exact_nullifier_aafi::field_value_preimage` are **DELETED,
    /// not deprecated**. Lanes 0/1 (the kernel u64 lane) are byte-identical across all three epochs.
    ///
    /// ⚠ **WHY THIS BUMP IS NOT OPTIONAL.** The CELL BYTES did not move; the PROJECTION did. So a
    /// pre-v14 store still DECODES, and that is exactly the hazard: every persisted
    /// `TurnReceipt::{pre,post}_state_hash`, every stored rotated `state_commit` and every
    /// checkpointed consensus anchor was computed under the epoch-13 projection and no longer equals
    /// a recomputation. A store that loads and quietly disagrees with itself is worse than one that
    /// refuses. **This is a RE-GENESIS.**
    ///
    /// What does NOT move: no descriptor re-emits and no VK rotates. The 184-limb nine-lane geometry
    /// was already emitted (`e662ade32`) — `layout_generated::ROTATED_FIELD_LANE_COL` already gives
    /// each field nine columns, the setField members already publish eight completion lanes (PIs
    /// 46..=53, the ninth at column `176 + slot`) and the absorption chain already folds `176..=183`
    /// into `state_commit`. The producers were writing the dead octet into eight of those nine and
    /// leaving the ninth at ZERO — consistent, and vacuous. Audited across all 174 members of the
    /// three deployed registries: the fields lane columns carry exactly three constraint species —
    /// `colEq` freezes, the Poseidon2 absorption, and the setField PI publications. No constant pin,
    /// no arithmetic relation to lane 0, and **no range check** (see the residual note below).
    ///
    /// ⚠ **NAMED RESIDUAL — the `< 2^28` free-lane property is a PRODUCER invariant, not an AIR one.**
    /// There is not one range lookup on any rotated block column in any deployed member, so nothing
    /// in-circuit forces a witness's fields lanes into the encoder's IMAGE. **A producer invariant
    /// establishes nothing for the party relying on the proof**: `fieldToLanes9_injective` quantifies
    /// over 32-byte VALUES, and an adversarial prover never applies the encoder — it writes nine
    /// committed columns directly, and off-image vectors are admissible in-AIR. RE-MEASURED 2026-07-31
    /// over all 186 emitted members and pinned by `circuit/tests/field_lanes9_canonicity_gate.rs`
    /// (which also RED-PROOFS its own reader against a planted lane lookup).
    ///
    /// ⚑ **AND THE REPAIR PRICED HERE — "7 × `< 2^28` lookups per field" — DOES NOT CLOSE IT.**
    /// Those seven are necessary and NOT sufficient, and the counterexample is one lane wide:
    /// `[0,0,0,0,0,0,0,0,3·2^24]` has every free lane below `2^28`, so all seven lookups accept it,
    /// yet its carry digit `3` makes the decoder restore `decLo = 0 + 3p = 6039797763`, which exceeds
    /// `2^32`, wraps in the `u32` view, and decodes byte-for-byte to `field_from_u64(1744830467)`.
    /// **In that witness the welded v1 face column reads 0 while the committed nonet decodes to
    /// 1744830467** — one accepted proof, two contradictory answers to "what is `fields[slot]`".
    ///
    /// The AIR obligation that IS sufficient is `Dregg2.Circuit.FieldLanes9.Canonical9`, three legs,
    /// proved EXACTLY the encoder's image by `canonical9_iff_in_image` (with `canonical_fieldToLanes9`
    /// the completeness pole and `lanes9ToField_injOn_canonical` the soundness one, all
    /// `#assert_axioms`-clean):
    ///
    /// 1. `FreeLanesRanged` — lanes 2..8 below `2^28`. **Seven range lookups per field.**
    /// 2. `PinnedLanesField` — lanes 0/1 are BabyBear elements. Free; a column is one.
    /// 3. `NoWrap` — `decLo`/`decHi` below `2^32`. **Not a range check on any lane**: a joint
    ///    condition on lane 0, lane 1 and lane 8's top nibble, and the leg the exhibit breaks.
    ///
    /// Emitting leg 3 needs seven aux columns per (block, slot) past the appendix — `r`, `q0`, `q1`,
    /// `v0`, `v0b`, `v1`, `v1b` — with `L8 = (q0 + 4·q1)·2^24 + r`, `q·(q−1)·(q−2) = 0`,
    /// `v = q(q−1)/2 · L`, `vb = v + 2·q(q−1)/2`, and range lookups `r < 2^24`, `v,vb < 2^28`.
    /// That is `112` aux columns (a multiple of 7, so the registry's width discipline survives),
    /// `112` gates and `192` lookups per member across 174 members: a descriptor re-emit and a VK
    /// rotation, NOT a re-genesis — the committed geometry and every anchor stay put, only the AIR
    /// gets stricter. It also needs `WIDE_RANGE_WIDTHS` / `CUSTOM_RANGE_WIDTHS` extended with 24 and
    /// 28. **That work is not done**; nothing above it is.
    ///
    /// ─────────────────────────────────────────────────────────────────────────────────────────
    /// ⚑ **14 → 15, 2026-07-31: A2/A3 — THE NOTE ACCUMULATOR LEAVES MOVED.**
    ///
    /// `NullifierSet::root8` and `CommitmentSet::root8` — the two values
    /// `dregg_turn::state_commit::consensus_state_commitment` folds into every signed
    /// `TurnReceipt::{pre,post}_state_hash` — left the arity-3 `CanonicalHeapTree8` leaf
    /// `(fold_bytes32_to_bb(key), split_u64(value).0, next)` for the exact tagged linked leaf
    /// `dom ‖ addr17 ‖ value4 ‖ next17`. The address was a 256→31-bit fold (A2) and the value a
    /// 64→30-bit truncation (A3); both are now carried at full width by `u16` limbs, and the
    /// successor POINTER is wide too, so the absence bracket survives the widening.
    ///
    /// **WHAT MUST BE RE-GENESISED:** every persisted accumulator root, every stored
    /// `TurnReceipt` state hash, every `AttestedRoot`, and the durable
    /// `nullifier_set_root`/`commitments_root` columns. A store at epoch 14 REFUSES to load
    /// rather than reinterpreting bytes minted under the old leaf.
    ///
    /// **WHAT DOES NOT MOVE:** no descriptor, no fingerprint, no verifier key. Nothing threaded
    /// either root into a map-op: the SDK builds the noteSpend grow-gate's BEFORE leaves itself
    /// with a hard-coded existence bit (`HeapLeaf::entry(*nf, BabyBear::new(1))` —
    /// `sdk/src/full_turn_proof.rs:397`, `:1022`, `:1135`), so the executor root and the
    /// in-circuit tree already disagreed whenever `split_u64(value).0 != 1`; and the noteCreate
    /// grow-gate's BEFORE set is always `&[]` (`full_turn_proof.rs:422`,
    /// `cipherclerk.rs:5812`), so the commitments root never reached a circuit at all. The
    /// "byte-for-byte agreement with the grow-gate is load-bearing" that both call sites
    /// documented as the blocker was a constituency that did not exist.
    ///
    /// **ALSO NEW, AND CONSENSUS-VISIBLE:** the committed roots are now append-ORDER dependent
    /// (they are the AAFI fold). Every reconstruction must go through the persisted `seq`
    /// column — `NullifierSet::from_records` / `CommitmentSet::from_records`, which is what
    /// `Store::faithful_nullifier_root`, `plan_faithful_nullifier_successor` and
    /// `node::executor_side_state_persistence` already do. A rebuild that re-inserts in storage
    /// order produces a different, wrong root; that is asserted as a pole rather than assumed.
    /// ─────────────────────────────────────────────────────────────────────────────────────────
    /// ⚑ **15 → 16, 2026-08-01: THE MEMBERSHIP TREE IS 8 FELTS WIDE (felt-width finding #9).**
    ///
    /// Every node of the 4-ary Poseidon2 `MerkleMembership` tree was **one BabyBear felt**:
    /// `hash_4_to_1` ran a genuine 16-wide permutation and returned `state.state[0]`;
    /// `generate_merkle_poseidon2_trace` chained that single felt level to level (the production
    /// root); the descriptor's parent lookup carried the arity-4 chip `out0` alone; and
    /// `compress_member` truncated the leaf the same way. A codomain of ~2^30.9 is
    /// second-preimaged in ~2^31 and **collided in ~2^15.5** — an attacker who contributes to or
    /// mints a subtree finds a second child quadruple with the same parent and presents a
    /// distinct authentication path reaching the SAME authorized root for a key that was never in
    /// the set. `circuit/tests/membership_forge_tooth.rs` exhibits that collision and the forged
    /// path it buys, then shows the widened fold refusing both.
    ///
    /// The node is now `node8_4ary(c0,c1,c2,c3) = A16(A16(c0‖c1) ‖ A16(c2‖c3))` — the arity-16
    /// `node8` absorb the deployed heap/cap/fields trees already ride — with all eight output
    /// lanes bound at every level, an 8-lane chain, and an 8-felt leaf.
    ///
    /// **WHAT MUST BE RE-GENESISED:** every persisted `SenderAuthorized { PublicRoot }`
    /// authorized-set root slot value, and every stored `MerkleMembership` / blinded-membership
    /// proof blob. The 32-byte root slot encoding CHANGED with the tree: it was ONE felt in the
    /// low four little-endian bytes with 28 zero bytes, and is now EIGHT canonical `u32` LE limbs
    /// filling the slot exactly (injective — every BabyBear canonical value is `< 2^31 < 2^32`).
    /// A store at epoch 15 REFUSES to load rather than reinterpreting a one-felt root as the low
    /// limb of an 8-felt one.
    ///
    /// **WHAT MOVES BESIDES THE STORE:** the descriptor, its fingerprint and its verifier key.
    /// `merkle-membership-4ary-general.json` (trace width 11, 2 PIs) and
    /// `blinded-membership-4ary-depth{2,8}.json` (width 27, 2 PIs) are DELETED and replaced by
    /// `merkle-membership-4ary-wide-general.json` (width 90, 16 PIs) and
    /// `blinded-membership-4ary-wide.json` (width 99, 16 PIs). The wire dispatch prefixes changed
    /// too, so a pre-cutover proof identity answers `UnknownAir` and is REFUSED rather than
    /// reinterpreted under a descriptor with different semantics.
    ///
    /// **WHAT DOES NOT MOVE:** the in-AIR sender-leaf weld
    /// (`CarrierOctetGates.lean::withMembershipPubkeyCompress` / `pubkeyCompress1Spec`) is stated
    /// at `A(pubkey8 ‖ 0⁸)[0]`, and lane 0 of the widened `compress_member` is bit-identical to
    /// the old return, so that gate holds unchanged — it is now a lane-0 projection of a leaf the
    /// membership STARK binds in full width. The teeth PIs 50/51 remain unpinned; that is a
    /// SEPARATE wound.
    ///
    /// ---
    ///
    /// **EPOCH 17 — the sorted-set NON-MEMBERSHIP (neighbor-adjacency) tree, same wound, same
    /// cure.** Epoch 16 named the adjacency tree as "a DIFFERENT, still one-felt chained tree with
    /// no wide Lean twin on disk". It is now widened and the one-felt path is DELETED.
    ///
    /// Every node of `dregg-membership-adjacency::poseidon2-v1` was one BabyBear felt:
    /// `poseidon2::hash_2_to_1` returned `state.state[0]`; `adjacency_walk` chained that single
    /// felt; the descriptor's per-level lookup was `chipLookupTupleNarrow [left, right] par` (the
    /// arity-2 NARROW bus, `out0` alone); `adjacency_compress` truncated each leaf to lane 0; and
    /// this crate's own note above pointed at `narrow_felt_from_slot_low4` for the root. Codomain
    /// 30.907 bits ⇒ **collision 2^15.45**, second-preimage 2^30.91.
    ///
    /// ⚑ The collision is a DOUBLE SPEND, not merely a forged membership: this gate certifies
    /// ABSENCE. An attacker mints a leaf pair whose one-felt parent collides with a genuine
    /// adjacent leaf pair of the committed tree, presents it at those same indices — so the
    /// consecutiveness tooth is satisfied HONESTLY — and chooses it to straddle a key that IS in
    /// the set. `circuit/tests/adjacency_forge_tooth.rs` exhibits exactly that at the deployed
    /// parameter (a real collision in 20,879 evaluations, ~2^14.3) and shows `node8` refusing it.
    ///
    /// The node is now `adjacency_node8(l, r) = A16(l ‖ r)` — one arity-16 `node8` absorb, since
    /// two 8-felt children are exactly `CHIP_RATE = 16` felts — with all eight output lanes bound
    /// at every level, an 8-lane chain (was ONE window), and 8-felt leaves as well as root.
    /// **Collision 2^123.63**, second-preimage 2^247.26.
    ///
    /// **WHAT MUST BE RE-GENESISED AT 17:** every persisted sorted-set / non-membership predicate
    /// commitment (`WitnessedPredicateKind::NonMembership`, the `SortedNeighborNonMembership` and
    /// `CredentialSetMembership` revocation legs), and every stored `adjacency_proof` blob. The
    /// 32-byte set-commitment encoding CHANGED with the tree: it was ONE felt in the low four
    /// little-endian bytes with 28 zero bytes, and is now EIGHT canonical `u32` LE limbs filling
    /// the slot exactly (`membership_verifier::adjacency_commitment_bytes`). Widening the tree
    /// while the boundary re-narrowed the root would have bought nothing.
    ///
    /// **WHAT MOVES BESIDES THE STORE:** `by-name/adjacency-membership.json` (trace width 18,
    /// 5 PIs) is DELETED and replaced by `by-name/adjacency-membership-wide.json` (width 88,
    /// 26 PIs). The descriptor NAME changed (`dregg-membership-adjacency::poseidon2-v1` →
    /// `dregg-membership-adjacency-wide::node8-v1`), so a pre-cutover proof identity resolves to
    /// `None` and is REFUSED rather than reinterpreted. `circuit/src/membership_adjacency_air.rs`
    /// — 188 lines publishing the retired 18-column layout with zero consumers — is DELETED.
    ///
    /// ⚠ **AND THE BRACKET MOVED WITH IT.** The strict `lower < candidate < upper` check compared
    /// one `u32`; it is now LEXICOGRAPHIC over the full 8-felt leaf digest
    /// (`membership_verifier::adjacency_leaf_order`), and a prover's tree must be sorted by that
    /// same order. A tree sorted by lane 0 alone has gaps that do not mean what the bracket reads.
    ///
    /// ⚠ **WHAT THIS EPOCH DOES *NOT* CLOSE — say it out loud.** The live in-circuit
    /// double-spend gate for `noteSpend` is NOT this tree: it is `Ir2Air::MapAbsent`, the Indexed
    /// Merkle Tree pointer bracket in `circuit/src/descriptor_ir2.rs`, reached through
    /// `noteSpendVmDescriptor2R24`. Its roots, leaf digests and node folds are ALREADY `node8` —
    /// but `MA_KEY`, `MA_LO_ADDR` and `MA_LO_NEXT` are **one felt each**, so the sort key and the
    /// IMT pointer are 31-bit while everything around them is 247-bit. That is a live finding of
    /// this same class with its own proved-and-unlanded Lean emitters already on disk
    /// (`Emit/LexCompare8Emit.lean`, `Emit/HeapLeafWideEmit.lean`,
    /// `Circuit/MapAbsentImtGateWide.lean`). It is NOT fixed here.
    ///
    /// # Epoch 19 — `hash_bytes`' PREIMAGE became injective (2026-08-01)
    ///
    /// `dregg_circuit::poseidon2::hash_bytes` was `hash_many(BabyBear::from_bytes_packed(data))`,
    /// and that composition was collidable at **cost 0** in two independent ways:
    ///
    /// 1. **the NUL-append.** The packer walked the input in 4-byte strides and ZERO-FILLED the
    ///    final partial chunk, while `hash_many` tagged `state[4]` with the FELT count — so
    ///    `hash_bytes(b"foo") == hash_bytes(b"foo\0")` and `hash_bytes(b"f") ==
    ///    hash_bytes(b"f\0\0\0")`. Append a NUL; the digest does not move.
    /// 2. **the mod-`p` chunk alias, AT EQUAL LENGTH.** Each chunk was a `u32` reduced mod
    ///    `p = 0x78000001 < 2^32`, so `01 00 00 78` packed to exactly `p` and collided with
    ///    `00 00 00 00`. `2^32 − p = 2281701375`, i.e. **53.1%** of chunks had a `+p` sibling. No
    ///    length tag of any kind separates these, which is why the repair changed the RADIX.
    ///
    /// The preimage is now `BabyBear::bytes_to_lanes`: a four-lane base-`2^16` BYTE-COUNT header
    /// then the bytes in little-endian `u16` pairs, every lane `< 2^16 < p` so nothing reduces.
    /// Lean authority `Dregg2.Circuit.BytesLanes` — `lanesToBytes_bytesToLanes` is a TOTAL decoder
    /// and a machine-checked LEFT INVERSE, `bytesToLanes_injective` its corollary. Not a hash
    /// bound. Old-admits/new-rejects for both collisions:
    /// `circuit/tests/bytes_lanes_injective.rs`, and at the named consumer
    /// `sandstorm-bridge/tests/var_nul_append_inclusion_forgery.rs` (serving a grain's
    /// `/var` card as `value ‖ "\0"` used to VERIFY under the honest root; it is now REFUSED).
    ///
    /// **WHAT MUST BE RE-GENESISED AT 19:** every persisted state commitment that `hash_bytes`
    /// reaches — `turn::rotation_witness:349` (receipt hash → MMR leaf → `iroot`),
    /// `exec_lean::nullifier::addr_of` (→ the nullifier root), and
    /// `cell::program::eval::hash_preimage32` (→ a committed `PreimageGate` / `KeyRotationGate`
    /// slot). Outside the ledger: every grain `/var` `data_root` (`sandstorm_bridge::cell` —
    /// then `{var_addr, var_value_felt}`, both DELETED 2026-08-03 when that commitment moved
    /// to the eight-lane `{var_coll, var_leaf_digest8}` under a `CanonicalHeapTree8` root and
    /// the wire prefix went `heap1…` → `heap8…`), every `bucket_root` /
    /// `content_root` hex (`storage::bucket_commitment`, `starbridge-apps/site-host`), every
    /// zkOracle `content_commit` / `template_commit`, and every `wasm` `fact_hash` reaching
    /// `PI_FACT_COMMITMENT`. A store at epoch 18 REFUSES to load rather than reinterpreting a
    /// root computed under the aliasing preimage.
    ///
    /// **WHAT DOES *NOT* MOVE: no VK rotates and no descriptor is re-emitted.** Measured across
    /// `metatheory/` on 2026-08-01: **no emitted AIR recomputes a byte packing.** Every Lean hash
    /// carrier is felt- or `Nat`-domain (`hash : List ℤ → ℤ`); the "in-AIR `hash_bytes` recompute"
    /// named at `circuit/src/effect_vm/authority_digest_weld.rs:54` is a felt-domain chip lookup
    /// over two floor felts; and `Dregg2.Deos.InAirAuthorityDigestSelector` calls the byte-sponge
    /// version *"the named, genuinely-VK-affecting remaining work"* — not built. So this is a
    /// producer-side flag day, and it is strictly cheaper now than after that recompute lands.
    /// (`ZKORACLE_MAX_BODY_LIMBS` is unmoved at 1024; the BYTE capacity it buys halves to 2040,
    /// stated at the constant rather than silently doubled — the price of 2 bytes/felt.)
    ///
    /// ⚠ **WHAT THIS EPOCH DOES *NOT* CLOSE.** `hash_bytes` still squeezes ONE felt.
    /// `log2(p) = 30.906891`, so a *searched* collision costs the birthday bound **`2^15.4534`**
    /// ≈ 44,900 evaluations — milliseconds. That is the `Digest1` shape
    /// `docs/DESIGN-canonical-byte-felt-codec.md` §2.3 bans by name; it is a DIFFERENT defect from
    /// the two above, and **neither fix reaches the other** — no widening of the squeeze removes
    /// an append-collision in the preimage, and no repair of the preimage removes a birthday
    /// collision in a 31-bit codomain. Its fix is the `HeapLeaf` `addr`/`value` widening and the
    /// `MapOp` value width in the emitted AIR (a constraint change), owned by that campaign.
    /// `poseidon2::hash_bytes_8` is the 8-felt companion (`2^123.63`) for sinks that can take it.
    /// # Epoch 20 — the present-cell-set KEY (2026-08-01)
    ///
    /// `turn::rotation_witness::cells_root` stopped keying present-cell existence leaves by
    /// `heap_addr(CELLS_COLLECTION, hash_bytes(id))` — ONE ~30.9-bit BabyBear felt per 32-byte
    /// `CellId` — and became the exact tagged-linked-leaf accumulator its four siblings already
    /// were (`FLI2`/`FLN2`/`FLE2`, depth 16, arity 4, eight lanes), keyed by the id's sixteen
    /// little-endian `u16` limbs: `2^256` **on the nose**, injective, nothing reduced.
    ///
    /// **WHY, and it was not a width nit.** `assert_addr_unique` (release-active since
    /// 2026-07-28) *panics* on a repeated address rather than silently deduping. Correct — a
    /// dedup makes a cell's removal invisible to the anchor — but shipping it over a key an
    /// attacker can collide converted a silent double-spend into a **$0 permanent consensus
    /// halt**: `CellId::derive_raw` is BLAKE3 over an attacker-chosen `(public_key, token_id)`,
    /// `Effect::CreateCell` checks only `balance == 0` (no possession check, no token registry,
    /// no rate limit — `token_id` alone is a free grinding domain), and `cells_root` is on the
    /// unconditional per-turn anchor path. ~2^15.5 offline folds plus two ordinary cell creations
    /// panicked every node's finality executor into `FatalIntegrity`, block unacknowledged,
    /// deterministically, across restarts. An injective key makes the refusal UNREACHABLE
    /// instead of merely fail-closed.
    ///
    /// **WHAT MUST BE RE-GENESISED AT 20:** every persisted `pre_state_hash` / `post_state_hash`
    /// and every stored `TurnReceipt` carrying them — the cells-root group is limb 0 ‖ 169..=175
    /// of the rotated block, so the anchor value moves on EVERY turn, including turns that create
    /// no cell. Executor signatures and federation receipt QCs over those anchors do not
    /// re-verify and are not migrated.
    ///
    /// **WHAT DOES *NOT* MOVE:** no VK rotates and no descriptor is re-emitted. Nothing in any
    /// circuit recomputes this key — the rotated trace generator overwrites the whole cells group
    /// with its own in-circuit accounts tree (which production always feeds `before_accounts =
    /// &[]`), and no verifier opens `cells_root`. The wide object was already Lean-proved and
    /// already on disk; this epoch REGISTERS a consumer of it, exactly as
    /// `Circuit/MapOpWideKeyPigeonhole.lean` says the kind-D residual requires.
    ///
    /// ⚠ **WHAT THIS EPOCH DOES *NOT* CLOSE.** The per-cell heap tree (`CellState::heap_map`,
    /// rotated limb 28) still addresses by the one-felt `heap_addr`, and so does the wasm
    /// light-client `verify_slot_opening` that recomputes it. That tree IS opened in-circuit
    /// (`heapWriteVmDescriptor2R24` recomputes `heap_addr` in-row), so widening it is a VK
    /// rotation and a descriptor re-emit — a different lane from this one.
    ///
    /// # Epoch 21 — the OWNER-KEY NONET (2026-08-01)
    ///
    /// The 32-byte → BabyBear-lane packer stopped being the `8+8+8+6 = 30` bits/limb **octet** and
    /// became the base-`2^29` **nonet** (`dregg_commit::typed::canonical_32_to_lanes_9`, the Rust
    /// twin of `Dregg2.Circuit.KeyLanes9.keyToLanes9`). Four byte-identical re-implementations
    /// moved together: `dregg_commit::typed`, `dregg_cell::commitment`, `dregg_storage::commitment`,
    /// and the copy inlined in `circuit/src/effect_vm/trace.rs`.
    ///
    /// **WHY, and it is not a width nit either.** `& 0x3F` discarded bits 6-7 of bytes 3, 7, …, 31
    /// — sixteen source bits — so every input had `2^16 - 1` siblings with a bit-identical lane
    /// vector, reachable by one XOR. Among the values that octet actually carried the collision
    /// cost was **zero**, not `2^120`: an Ed25519 public key keeps its x-sign in bit 7 of byte 31,
    /// one of the unread bits, so a key and its negation — a keypair whose private half is
    /// `-a mod L`, fully attacker-controlled — packed to ONE octet. Range-checking eight lanes
    /// could not have repaired it (`p^8 < 2^256`). The nonet's image is exactly `2^256` and its
    /// injectivity is a Lean theorem with a total decoder and a machine-checked left inverse.
    ///
    /// **WHAT MUST BE RE-GENESISED AT 21:** every persisted `pre_state_hash` / `post_state_hash`
    /// and every stored `TurnReceipt` carrying them. The packer feeds `compress_member` (every
    /// membership-domain Merkle leaf, interior node and committed root) and `canonical_32_to_felts_4`
    /// (the `turn_hash`, `previous_receipt_hash`, `federation_id` and `owner_cell_id` PI bindings),
    /// so the anchor moves on EVERY turn. Executor signatures and federation receipt QCs over
    /// those anchors do not re-verify and are **not migrated** — `enforce_canonical_state_schema_epoch`
    /// refuses a store stamped 20 rather than reinterpreting it.
    ///
    /// **WHAT DOES *NOT* MOVE:** no chip arity, no table, no descriptor width, no PI count. The
    /// membership absorb is still one `CHIP_NODE8_ARITY = 16` permutation (`9 + 7`, was `8 + 8`)
    /// and the id fold is off-AIR — measured: the rotation emitter carries no federation-id term
    /// and the boundary constraints only PIN the four aux columns to their PIs.
    ///
    /// ⚠ **WHAT THIS EPOCH DOES *NOT* CLOSE, and it is the load-bearing half.** `B_PUBKEY_OCTET`
    /// is **eight columns wide in the deployed 184-limb geometry**, and the nonet's ninth lane has
    /// no column to live in. The 187-limb layout that gives it one (in-block limb 186) is PROVED
    /// and committed in Lean (`RotatedLayout.rotated187`, `94532b3a4`) and **not emitted**: the
    /// emitter `metatheory/EmitLayoutManifest.lean` transitively imports
    /// `Dregg2/Circuit/Emit/EffectVmEmitRotationWide.lean`, which is red on three `sorryAx`
    /// axiom-hygiene failures under another lane's edit. So at epoch 21 the nonet reaches the
    /// membership leaf and the id folds in full, and `state_commit` still binds only the low eight
    /// lanes of the owner key. `circuit/tests/key_nonet_ninth_lane_reaches_the_anchor.rs` is the
    /// gate that flips when the geometry is emitted; it is keyed on `NUM_PRE_LIMBS`, so it cannot
    /// rot quietly the way the hand-carried `B_CHAIN_BASE` did across `178 → 184`.
    /// ## Epoch 22 — the receipt-log root (`iroot`) becomes an 8-lane fold, and its EMPTY root
    /// stops being zero
    ///
    /// **WHAT MOVES:** every persisted `pre_state_hash` / `post_state_hash` and every stored
    /// `TurnReceipt` carrying them, on BOTH paths. `turn::rotation_witness::iroot` is no longer a
    /// zero-seeded 1-felt chain over 1-felt leaves; it is lane 0 of
    /// `poseidon2::receipt_chain_root_8` (Lean twin
    /// `Dregg2.Lightclient.ReceiptChain8.rchain8`, `rchain8_binds_or_collides` at 2^123.63), whose
    /// empty-log root is the domain-tagged `A2[RCE2, 0]` rather than `BabyBear::ZERO`. Since
    /// `state_commit::consensus_ctx` pins the EMPTY root on the classical path, that constant moving
    /// is itself enough to move every classical anchor. Executor signatures and federation receipt
    /// QCs over epoch-21 anchors do not re-verify and are **not migrated** —
    /// `enforce_canonical_state_schema_epoch` refuses a store stamped 21 rather than reinterpreting
    /// it.
    ///
    /// **WHAT DOES *NOT* MOVE:** no chip arity, no table, no descriptor width, no PI count, no VK.
    /// `iroot` is witness-carried: no AIR gate constrains its value (`weldsAt` covers `base+1..11`
    /// and `B_CAP_ROOT`; `rotPins` never names `B_IROOT`; the Rust descriptor audit treats it as a
    /// fresh absorbed limb and never as a digest). So this is a producer/value change only.
    ///
    /// ⚠ **WHAT THIS EPOCH DOES *NOT* CLOSE — the same shape as the note above, and the same
    /// blocker.** `B_IROOT` is ONE column and `ROTATED_PADS` is empty, so lanes 1..7 of the fold are
    /// computed and DISCARDED at the wire: the value reaching the signed anchor is still one felt
    /// (collision 2^15.45, measured at 71,133 evaluations / 0.86 s in
    /// `turn/tests/iroot_wide_old_admits_new_rejects.rs`, which builds two well-formed receipt logs
    /// with a byte-identical signed anchor). The cutover is named in
    /// `rotation_witness::IROOT_LANES_1_TO_7_UNABSORBED` and gated by
    /// `the_residual_is_a_gate_not_a_note`, which is keyed on `NUM_PRE_LIMBS` so it flips the day
    /// the geometry is emitted. Verified 2026-08-01, not relayed: `lake env lean --run
    /// EmitLayoutManifest.lean` fails to LOAD — `EffectVmEmitRotationWide.olean` does not exist —
    /// so `emit_descriptors.py` cannot run at all while that lane's edit is in flight.
    ///
    /// ## Epoch 23 — the Poseidon2 hash-LOCK slot goes eight lanes (2026-08-01)
    ///
    /// `cell::program::eval::hash_preimage32` — the shared digest behind
    /// `StateConstraint::PreimageGate` and `StateConstraint::KeyRotationGate` — computed
    /// `felt_to_bytes32(poseidon2::hash_bytes(preimage))` for `HashKind::Poseidon2`: **ONE
    /// ~30.906891-bit BabyBear felt in bytes 0..4, twenty-eight of the thirty-two committed bytes
    /// left ZERO**, while the `HashKind::Blake3` arm sitting next to it in the same `match` used
    /// all thirty-two. It is now `digest8_to_bytes32(poseidon2::hash_bytes_8(preimage))` — the
    /// same `Digest8` packing `compute_canonical_capability_root_wide` and the wide
    /// `heap_root`/`fields_root` already use.
    ///
    /// **WHAT THE NARROW SLOT HANDED AN ATTACKER.** Both constraints are hash-LOCKS, whose entire
    /// content is "only a holder of the committed secret can open this":
    ///
    /// * `PreimageGate` — a slot commits `H(secret)`; a turn exhibiting `secret` passes. Against a
    ///   PUBLISHED commitment that is a second preimage of a 30.906891-bit target: `2^30.91`
    ///   ≈ 1.5e9 Poseidon2 evaluations, **hours on one core**, and the opener never learns the
    ///   real secret. A party who also chose the commitment gets the birthday form, `2^15.4534`
    ///   ≈ 44,900 evaluations, and can open one lock with two different "secrets".
    /// * `KeyRotationGate` — worse, because the forged preimage is not merely accepted, it is
    ///   **INSTALLED**: the arm checks `hash_preimage32(kind, preimage) == old_fields[digest_slot]`
    ///   and then requires `new_state.fields[current_slot] == preimage`. A colliding 32-byte value
    ///   becomes the cell's current key set at the costs above.
    ///
    /// At eight lanes the image is `8 * 30.906891 = 247.255128` bits: collision `2^123.63`, second
    /// preimage `2^247.26`. Measured old-admits/new-rejects (a real collision, two well-formed
    /// preimages, the retired encoding ACCEPTING a preimage the committer never chose, and the
    /// key-rotation arm INSTALLING it): `cell/tests/preimage_gate_wide_old_admits_new_rejects.rs`.
    ///
    /// **WHAT MUST BE RE-GENESISED AT 23:** every persisted `CellState.fields[i]` holding a
    /// Poseidon2-tagged `PreimageGate` commitment or `KeyRotationGate` next-keys digest — and
    /// therefore every state commitment over such a cell. A store stamped 22 REFUSES to load
    /// rather than reinterpreting; an un-re-genesised slot is fail-CLOSED (no preimage opens it
    /// any more), never silently narrow. `HashKind::Blake3` slots are untouched.
    ///
    /// **Outside the ledger, same commit, same cause:** every zkOracle `content_commit` /
    /// `template_commit` (`zkoracle-prove`, now `[BabyBear; 8]` — the serde shape changed, so an
    /// epoch-22 serialized attestation REFUSES to deserialize rather than reinterpreting), every
    /// `attested-dm` / `deos-hermes` `attestation_commitment` receipt id, and every
    /// `dungeon-on-dregg` narration `EmitEvent` `data[SLOT_ATTESTATION_COMMIT]` (and therefore
    /// every receipt hash over one).
    ///
    /// **WHAT DOES *NOT* MOVE: no VK rotates and no descriptor is re-emitted.** Independently
    /// re-measured 2026-08-01 for this cutover: there is **no emitted descriptor for the preimage
    /// gate at all** (`circuit/descriptors/by-name/` has none; `descriptor_by_name.rs`'s dispatch
    /// has no arm), the Lean models it as an opaque portal (`Dregg2.Exec.Program`'s `.preimageGate`
    /// is `ctx.revealedHash == new.scalar f`, pure equality over a §8 crypto-portal INPUT), and
    /// `Dregg2.Exec.DeployedConstraint` *refuses* to marshal the arms that read
    /// `revealed_preimage` at all. Same verdict as epoch 19's: `hash_bytes`' squeeze has no in-AIR
    /// counterpart anywhere in the tree.
    ///
    /// ⚠ **WHAT THIS EPOCH DOES *NOT* CLOSE.** The `hash_bytes` caller sweep classified every
    /// production caller; three (A) sites are named-and-not-migrated because their sink is one
    /// felt wide in a place Rust does not own, and each says so at its own definition:
    /// `exec_lean::nullifier::addr_of` (the `MapAbsent` IMT key — `MA_KEY`/`MA_LO_ADDR`/
    /// `MA_LO_NEXT`, Lean emit work, and it needs the base-2^29 NONET, not eight lanes, because a
    /// KEY needs injectivity over 256 bits and 247.26 < 256), `wasm`'s `fact_hash` → column
    /// `PREDICATE_SYM` of the deployed `predicate-arith*` goldens, and
    /// `sandstorm_bridge::cell::{var_addr, var_value_felt}` (whose whole `/var` ROOT is one felt,
    /// so widening only the leaves would be a containment below the bar).
    ///
    /// ## Epoch 24 — the finalization vote covers a per-turn value (2026-08-07)
    ///
    /// `dregg_types::finalization_vote_signing_message` moved v3 → v4 and now absorbs the
    /// finalized block's `receipt_stream_root`:
    ///
    /// ```text
    ///   v3:  "dregg-finalization-vote-v3" ‖ block_id ‖ merkle_root
    ///   v4:  "dregg-finalization-vote-v4" ‖ block_id ‖ merkle_root ‖ 0x00 | 0x01‖<32 bytes>
    /// ```
    ///
    /// **WHY, in one line:** no committee signature anywhere in this tree covered a per-turn
    /// value. The only preimage that absorbed `receipt_stream_root`
    /// (`AttestedRoot::signing_message`) receives exactly ONE push — the local node's — because
    /// `PeerMessage::AttestedRootUpdate` has zero handlers, while the quorum that DOES assemble
    /// signed a block id and a whole-ledger BLAKE3 image. So `dregg_federation::TurnAnchorV1`
    /// refused on every federation with `threshold > 1`.
    ///
    /// **WHAT REFUSES TO LOAD / WHAT MUST BE RE-GENESISED.** Every persisted
    /// `StoredAttestedRoot::finalization_quorum` signed under v3 is now a signature over a
    /// message no verifier reconstructs: `verify_finalization_quorum` REFUSES it (it does not
    /// reinterpret it), so an epoch-23 store's committee restart anchor fails closed and the
    /// node refuses to start on it. A store stamped 23 is refused by
    /// `enforce_canonical_state_schema_epoch` rather than migrated — re-genesis. The gossiped
    /// `FinalizationVote` wire also gained a field (postcard is non-self-describing), so a
    /// mixed-version mesh does not merely fail to agree, it fails to decode: **every node
    /// upgrades together, which is what a flag day means here.** The verified Lean quorum wire
    /// moved in the same commit (`VOTE := signer:ledgerRoot:streamRoot`); a v3 wire is `ERR`,
    /// fail-closed.
    ///
    /// **WHAT DOES *NOT* MOVE:** no VK rotates, no descriptor is re-emitted, no PI count
    /// changes, no chip arity moves. `receipt_stream_root` was already a field of both
    /// `AttestedRoot` and `StoredAttestedRoot` and is already in the attested-root preimage
    /// (v4, #80) — this epoch changes WHICH SIGNATURES cover it, not what it is.
    ///
    /// # Epoch 25 — SHIELDED SPEND PINS THE COMMITTED ACCUMULATOR (seam #15), 2026-08-07
    ///
    /// **WHAT SHAPE CHANGED.** `ShieldedTransferPayload` lost `merkle_root: u32` and
    /// `ShieldedInputPayload` gained `spend_wide_binding: [u32; 16]`, while `spend_proof` changed
    /// relation: it is now an `Ir2BatchProof` against the Lean-emitted
    /// `dregg-shielded-spend-complete-fsi2::v1` (`ShieldedSpendCompleteEmit.lean`, 557 columns,
    /// 25 PIs) instead of a `DslZkProof` against the retired 3-PI `dregg-shielded-spend-v1`.
    ///
    /// **WHY.** The retired `merkle_root` was the PROVER's choice of commitment-tree root and was
    /// compared against nothing — `ShieldedMerkleRootPin.root_substitution_forges`: build your own
    /// tree holding a note that was never committed, honestly prove membership at that tree's root,
    /// publish it. The executor now reads `note_shielded.root8()` from live state and judges every
    /// spend against it (`apply_shielded_transfer` GATE 0), so there is no field to forge.
    ///
    /// **WHAT REFUSES TO LOAD / WHAT MUST BE RE-GENESISED.** Postcard is non-self-describing: a
    /// pre-cutover `ShieldedTransferPayload` does not decode as a current one (a removed field, a
    /// widened input struct, different proof bytes) — it REFUSES rather than being reinterpreted.
    /// Every shielded-transfer `effects_hash` moves (the root was the first thing absorbed), so
    /// every receipt, executor signature, receipt QC and attestation over a turn containing one is
    /// invalid. A store stamped 24 is refused by `enforce_canonical_state_schema_epoch` rather than
    /// migrated — **re-genesis**, and the devnet is re-genesised with it.
    ///
    /// **WHAT DOES *NOT* MOVE:** no rotation-carrier limb is added, so the signed consensus anchor
    /// (`consensus_state_commitment`) is byte-identical and no VK in the rotation family rotates.
    /// Committing `note_shielded.root8()` into that carrier needs a fifth `V9RotationContext` root
    /// — a new base limb plus a completion octet in the Lean-emitted `EffectVmEmitRotationV3` — and
    /// is a SEPARATE VK epoch (the L1 carrier work), deliberately not folded in here.
    /// # Epoch 27 — EXCLUSION-BY-PAST: THE TIPS MAP CARRIES EVIDENCE PAIRS; AUTO-EVICT IS DELETED, 2026-08-08
    ///
    /// **WHAT SHAPE CHANGED.** `BlocklaceMeta::tips` (and `finality::CheckpointData::tips`) went
    /// from `HashMap<creator, BlockId>` to `HashMap<creator, CreatorTips>` — one tip per honest
    /// creator, a pinned incomparable PAIR per detected equivocator (the Cordial Miners Alg. 1:5
    /// two-tips floor, so the fork evidence is carried into later blocks' closures instead of
    /// sitting unreferenced). `LeaveReason::Evicted` is DELETED (constructed zero times), which
    /// shifts the postcard tag of `LeaveReason::Timeout`.
    ///
    /// **WHY.** Equivocator exclusion was a node-local live mutation (`auto_evict` on gossip
    /// arrival, mutating `participants` + threshold) — divergent across arrival orders (the
    /// F-CO-1 silent-fork door) and reverted by restart. It is now the papers' predicate over
    /// committed structure (`node(b) ∉ byz(⌊b⌋)`), evaluated per anchor closure inside τ; the
    /// participant set changes only through voted, finalized membership proposals.
    ///
    /// **WHAT REFUSES TO LOAD / WHAT MUST BE RE-GENESISED.** A store stamped 26 is refused by
    /// `enforce_canonical_state_schema_epoch` — **re-genesis**. (Postcard would also refuse the
    /// old `tips` blob shape rather than reinterpret it.) The gossip `Frontier` message's `tips`
    /// field changed identically: mixed-version committees cannot parse each other's frontiers,
    /// so all validators redeploy together. Nothing about proofs, VKs, or the consensus anchor
    /// moves.
    ///
    /// # Epoch 26 — THE SHIELDED VALUE LINK IS IN THE AIR; THE PEDERSEN LEG IS DELETED, 2026-08-07
    ///
    /// **WHAT SHAPE CHANGED.** `ShieldedTransferPayload` lost `input_legs`, `output_legs`,
    /// `output_range_proofs` and `conservation`; `ShieldedInputPayload` lost
    /// `legacy_value_binding`, `wide_value_binding` and `wide_value_proof`; `ShieldedLeg` is
    /// DELETED and replaced by `ShieldedOutputPayload { note_commitment }`.
    ///
    /// ⚑ **A SECOND SHAPE CHANGE, 2026-08-07 (change outputs).** The per-output `link_proof` field
    /// moved OFF `ShieldedOutputPayload` and onto `ShieldedTransferPayload::link_proof` — one link
    /// proof per TRANSFER, judged against the relation `outputs.len()` selects
    /// (`dregg-shielded-transfer-value-link::v1` for 1 output,
    /// `dregg-shielded-transfer-value-link-2out::v1` for 2). Conservation across two outputs is a
    /// JOINT statement, so per-output proofs cannot express a split: two of them would each
    /// separately claim the whole input value. The effects-hash preimage changed with it (the link
    /// proof is absorbed once, after the commitments), so a shielded transfer's effects hash
    /// differs from its pre-cutover value even at 1 output.
    ///
    /// **WHY.** Epoch 25 closed the spend-side theft and its lane named one residual it did not
    /// hide: *"the Pedersen leg's own `v` is bound to the STARK-side `v` only through this
    /// TRANSCRIPT, not by any circuit equality (`verify_value_link` is test-only)."* So a spender
    /// who genuinely owned a note worth `1` published legs committing to `1_000_000`,
    /// `verify_full_conservation_bytes` cleared `Σ C_in = Σ C_out` over those PROVER-CHOSEN legs,
    /// and nothing compared them to the note. That gap is not closable by a check — a BabyBear
    /// STARK cannot open a Ristretto point without non-native curve arithmetic in-AIR, and a
    /// Ristretto sigma protocol cannot open a Poseidon2 image without the hash in-group
    /// (`cell-crypto/src/value_link_zk.rs` records the same finding and names the exit). The
    /// Pedersen leg is therefore deleted and the value is bound where the spend already binds it:
    /// the Lean-emitted `dregg-shielded-transfer-value-link::v1`
    /// (`ShieldedTransferValueLinkEmit.lean`, 164 columns, 17 PIs) reads ONE set of canonical
    /// 16-bit limb columns for both the spent note's sixteen carrier lanes and the minted note's
    /// commitment. Range proofs went with the group that needed them — the limb cells' booleanity
    /// is forced in the AIR, so `0 ≤ v < 2^64` is a property of the trace.
    ///
    /// **WHAT REFUSES TO LOAD / WHAT MUST BE RE-GENESISED.** Postcard is non-self-describing: a
    /// pre-cutover `ShieldedTransferPayload` does not decode as a current one (four removed
    /// fields, a narrowed input struct, a replaced output struct) — it REFUSES rather than being
    /// reinterpreted. Every shielded-transfer `effects_hash` moves again (the leg groups, the
    /// range-proof group and the conservation blob all leave the preimage), so every receipt,
    /// executor signature, receipt QC and attestation over a turn containing one is invalid. A
    /// store stamped 25 is refused by `enforce_canonical_state_schema_epoch` rather than migrated
    /// — **re-genesis**.
    ///
    /// **WHAT ELSE RE-EMITS.** `dregg-shielded-transfer-value-link::v1` is a NEW descriptor; the
    /// shielded family's VK epoch rolls with it. The wide-value-binding SIDECAR relation is no
    /// longer on the transfer path (the link relation proves everything it proved about an input
    /// carrier, plus the tie to the output), so the sidecar's proof no longer rides the wire.
    ///
    /// **WHAT DOES *NOT* MOVE:** no rotation-carrier limb is added; the signed consensus anchor is
    /// byte-identical and no VK in the rotation family rotates.
    ///
    /// **WHAT A TRANSFER OUTPUT NOW IS.** `note_shielded` used to hold two shapes — Shield-minted
    /// Poseidon2 note commitments (spendable) and transfer-minted Ristretto points (not openable
    /// by any circuit, so value entering one was unrecoverable). It now holds ONE: every appended
    /// leaf is `hash_fact(v,[a,owner,rand])` and every appended leaf is spendable.
    pub const CANONICAL_STATE_SCHEMA_EPOCH: u64 = 27;

    /// Open a persistent store backed by a file on disk.
    ///
    /// Creates the file and all necessary tables if they don't exist.
    pub fn open(path: &Path) -> Result<Self> {
        let db = Database::create(path).map_err(|e| StoreError::Database(e.to_string()))?;
        let store = Self {
            db,
            fail_persist_block: std::sync::atomic::AtomicBool::new(false),
            fail_config_io: std::sync::atomic::AtomicBool::new(false),
            per_cell_head_cache: Default::default(),
        };
        store.initialize_tables()?;
        store.enforce_canonical_state_schema_epoch()?;
        store.enforce_poa_compact_authority_schema_v1()?;
        // Trust is checked before any reopen migration mutates derived indexes. A positive-floor
        // store opened without its external deployment policy refuses at this wall.
        store.audit_poa_compact_authority_v1(None)?;
        // This migration must precede any generic index rebuild: once a legacy
        // store has compacted records, their write sets are unavailable and an
        // absent provenance baseline is unreconstructable (fail before mutating
        // any secondary index).
        store.migrate_per_cell_receipt_head_index_v1()?;
        // One-time index-shape migration for stores written before the
        // (height, creator, ordinal) key (no-op on fresh/migrated stores).
        store.migrate_height_creator_index()?;
        store.rebuild_exact_fnsp_v3_online_index_on_open()?;
        store.audit_exact_fnsp_v3_faithful_bridge_on_open()?;
        store.validate_exact_fnsp_v3_receipt_authority_on_open()?;
        store.audit_finalized_receipt_cores_v1_on_open()?;
        store.audit_poa_signal_state()?;
        store.audit_poa_event_store()?;
        store.audit_poa_event_batch_store_v2()?;
        store.audit_poa_holding_consumptions()?;
        Ok(store)
    }

    /// Open a persistent store while supplying the independently authenticated PoA compaction
    /// committee history for this deployment.
    ///
    /// A store with a positive compaction floor cannot be opened through [`Self::open`]: its
    /// self-carried anchor rosters are evidence, not trust roots. Production derives `trust_policy`
    /// from deployment/genesis configuration held outside this database and supplies it on every
    /// restart. Every historical anchor must resolve to one exact policy root.
    pub fn open_with_poa_compact_trust_v1(
        path: &Path,
        trust_policy: &PoaCompactTrustPolicyV1,
    ) -> Result<Self> {
        let db = Database::create(path).map_err(|e| StoreError::Database(e.to_string()))?;
        let store = Self {
            db,
            fail_persist_block: std::sync::atomic::AtomicBool::new(false),
            fail_config_io: std::sync::atomic::AtomicBool::new(false),
            per_cell_head_cache: Default::default(),
        };
        store.initialize_tables()?;
        store.enforce_canonical_state_schema_epoch()?;
        store.enforce_poa_compact_authority_schema_v1()?;
        store.audit_poa_compact_authority_v1(Some(trust_policy))?;
        store.migrate_per_cell_receipt_head_index_v1()?;
        store.migrate_height_creator_index()?;
        store.rebuild_exact_fnsp_v3_online_index_on_open()?;
        store.audit_exact_fnsp_v3_faithful_bridge_on_open()?;
        store.validate_exact_fnsp_v3_receipt_authority_on_open()?;
        store.audit_finalized_receipt_cores_v1_on_open()?;
        store.audit_poa_signal_state()?;
        store.audit_poa_event_store()?;
        store.audit_poa_event_batch_store_v2()?;
        store.audit_poa_holding_consumptions()?;
        Ok(store)
    }

    /// Open an in-memory store (useful for testing).
    ///
    /// Data is lost when the store is dropped.
    pub fn open_in_memory() -> Result<Self> {
        let backend = redb::backends::InMemoryBackend::new();
        let db = Database::builder()
            .create_with_backend(backend)
            .map_err(|e| StoreError::Database(e.to_string()))?;
        let store = Self {
            db,
            fail_persist_block: std::sync::atomic::AtomicBool::new(false),
            fail_config_io: std::sync::atomic::AtomicBool::new(false),
            per_cell_head_cache: Default::default(),
        };
        store.initialize_tables()?;
        store.enforce_canonical_state_schema_epoch()?;
        store.enforce_poa_compact_authority_schema_v1()?;
        store.migrate_per_cell_receipt_head_index_v1()?;
        store.rebuild_exact_fnsp_v3_online_index_on_open()?;
        store.audit_exact_fnsp_v3_faithful_bridge_on_open()?;
        store.validate_exact_fnsp_v3_receipt_authority_on_open()?;
        store.audit_poa_compact_authority_v1(None)?;
        store.audit_finalized_receipt_cores_v1_on_open()?;
        store.audit_poa_signal_state()?;
        store.audit_poa_event_store()?;
        store.audit_poa_event_batch_store_v2()?;
        store.audit_poa_holding_consumptions()?;
        Ok(store)
    }

    /// Install or validate the v11 canonical-state epoch before any migration
    /// mutates secondary indexes.  An unmarked store is accepted only when all
    /// durable authorities capable of carrying cell/ledger state are empty.
    /// This is deliberately a re-genesis gate, not an in-place reinterpretation
    /// of V10 fields roots or V2 ledger roots.
    fn enforce_canonical_state_schema_epoch(&self) -> Result<()> {
        let read = self.db.begin_read()?;
        let (installed, commit_cursor) = {
            let metadata = read.open_table(tables::METADATA)?;
            (
                metadata
                    .get(tables::META_CANONICAL_STATE_SCHEMA_EPOCH)?
                    .map(|value| value.value()),
                metadata
                    .get(tables::META_COMMIT_CURSOR)?
                    .map(|value| value.value())
                    .unwrap_or(0),
            )
        };

        if let Some(epoch) = installed {
            if epoch == Self::CANONICAL_STATE_SCHEMA_EPOCH {
                return Ok(());
            }
            return Err(StoreError::Integrity(format!(
                "canonical state schema epoch {epoch} is incompatible with required epoch {}; \
                 re-genesis is required",
                Self::CANONICAL_STATE_SCHEMA_EPOCH
            )));
        }

        let authority_populated = commit_cursor != 0
            || !read.open_table(tables::COMMIT_LOG)?.is_empty()?
            || !read.open_table(tables::IDX_CELL_BY_ID)?.is_empty()?
            || !read.open_table(tables::CHECKPOINTS)?.is_empty()?
            || !read.open_table(tables::LEDGER_CHECKPOINTS)?.is_empty()?
            || !read.open_table(tables::ATTESTED_ROOTS)?.is_empty()?
            || !read.open_table(tables::BLOCKLACE_BLOCKS)?.is_empty()?
            || !read.open_table(tables::RECEIPT_CHAIN)?.is_empty()?;
        drop(read);

        if authority_populated {
            return Err(StoreError::Integrity(
                "populated store has no canonical state schema epoch; refusing to reinterpret \
                 pre-v11 fields roots / pre-v3 ledger roots (re-genesis required)"
                    .into(),
            ));
        }

        let write = self.db.begin_write()?;
        {
            let mut metadata = write.open_table(tables::METADATA)?;
            metadata.insert(
                tables::META_CANONICAL_STATE_SCHEMA_EPOCH,
                Self::CANONICAL_STATE_SCHEMA_EPOCH,
            )?;
        }
        write.commit()?;
        Ok(())
    }

    /// Initialize all tables in the database.
    fn initialize_tables(&self) -> Result<()> {
        let write_txn = self.db.begin_write()?;
        {
            // Federation tables.
            let _ = write_txn.open_table(tables::REVOCATIONS)?;
            let _ = write_txn.open_table(tables::ATTESTED_ROOTS)?;
            // Note tree tables.
            let _ = write_txn.open_table(tables::NOTE_COMMITMENTS)?;
            let _ = write_txn.open_table(tables::NOTE_COMMITMENT_RECORDS_V1)?;
            let _ = write_txn.open_table(tables::REVOCATION_RECORDS_V1)?;
            let _ = write_txn.open_table(tables::BRIDGED_NULLIFIERS_V1)?;
            let _ = write_txn.open_table(tables::REACTIVE_NULLIFIERS_V1)?;
            let _ = write_txn.open_table(tables::EXECUTOR_ACCUMULATOR_FRONTIERS_V1)?;
            let _ = write_txn.open_table(tables::EXECUTOR_REACTIVE_NULLIFIER_FRONTIERS_V1)?;
            let _ = write_txn.open_table(tables::EXECUTOR_RATE_LIMIT_SNAPSHOTS_V1)?;
            let _ = write_txn.open_table(tables::EXECUTOR_FACTORY_REGISTRY_SNAPSHOTS_V1)?;
            let _ = write_txn.open_table(tables::EXECUTOR_REACTIVE_REGISTRY_SNAPSHOTS_V1)?;
            let _ = write_txn.open_table(tables::FAITHFUL_NOTE_ROOT_HISTORY)?;
            let _ = write_txn.open_table(tables::NULLIFIERS)?;
            let _ = write_txn.open_table(tables::NULLIFIER_RECORDS_V1)?;
            let _ = write_txn.open_table(tables::FINALIZED_FAITHFUL_SPENDS)?;
            let _ = write_txn.open_table(tables::FINALIZED_FAITHFUL_SPEND_TURNS)?;
            // Empty until the exact-v3 flag-day seeding transaction installs a head reconstructed
            // from the complete durable append-record image.
            let _ = write_txn.open_table(exact_fnsp_v3_state::EXACT_FNSP_V3_STATE_HEAD)?;
            let _ = write_txn.open_table(exact_fnsp_v3_state::EXACT_FNSP_V3_APPEND_RECORDS)?;
            // Rebuildable exact-state online index: ordered predecessor positions, linked leaves,
            // sparse Merkle nodes, and immutable generation heads. Canonical authority remains the
            // signed frame + dense append image; these rows only remove replay from the live path.
            let _ = write_txn.open_table(exact_fnsp_v3_state::EXACT_FNSP_V3_ORDERED_POSITIONS)?;
            let _ = write_txn.open_table(exact_fnsp_v3_state::EXACT_FNSP_V3_LINKED_LEAVES)?;
            let _ = write_txn.open_table(exact_fnsp_v3_state::EXACT_FNSP_V3_SPARSE_NODES)?;
            let _ = write_txn.open_table(exact_fnsp_v3_state::EXACT_FNSP_V3_HEAD_HISTORY)?;
            // Full-history equality is audited at open/bootstrap. This singleton is the rolling
            // induction boundary that lets live faithful/exact admission stay O(1).
            let _ = write_txn
                .open_table(exact_fnsp_v3_faithful_bridge::EXACT_FNSP_V3_FAITHFUL_BRIDGE)?;
            let _ = write_txn.open_table(exact_fnsp_v3_frame_head::EXACT_FNSP_V3_ACTIVATION)?;
            let _ = write_txn.open_table(exact_fnsp_v3_frame_head::EXACT_FNSP_V3_FRAME_HEAD)?;
            let _ = write_txn.open_table(exact_fnsp_v3_frame_head::EXACT_FNSP_V3_FRAME_RECORDS)?;
            let _ = write_txn.open_table(exact_fnsp_v3_frame_head::EXACT_FNSP_V3_RECEIPT_HEADS)?;
            let _ = write_txn.open_table(finalized_receipt_core_v1::FINALIZED_RECEIPT_CORES_V1)?;
            let _ = write_txn.open_table(
                finalized_receipt_core_v1::FINALIZED_RECEIPT_CORE_BY_RECEIPT_INDEX_V1,
            )?;
            let _ = write_txn
                .open_table(finalized_receipt_core_v1::FINALIZED_RECEIPT_INDEX_BY_CORE_V1)?;
            let _ =
                write_txn.open_table(finalized_receipt_core_v1::FINALIZED_RECEIPT_CORE_HEADS_V1)?;
            // Checkpoint tables.
            let _ = write_txn.open_table(tables::CHECKPOINTS)?;
            // Ledger checkpoint table.
            let _ = write_txn.open_table(tables::LEDGER_CHECKPOINTS)?;
            // Blocklace tables.
            let _ = write_txn.open_table(tables::BLOCKLACE_BLOCKS)?;
            let _ = write_txn.open_table(tables::BLOCKLACE_META)?;
            // Node witness artifact tables.
            let _ = write_txn.open_table(tables::WITNESSED_RECEIPTS)?;
            // Durable receipt chain (the served /api/receipts* log + MMR source).
            let _ = write_txn.open_table(tables::RECEIPT_CHAIN)?;
            // Durable realm-substrate op log (realm-model persistence, replayed
            // on boot to reconstruct realm/instance/identity/catalog + head).
            let _ = write_txn.open_table(tables::REALM_LOG)?;
            // Durable commit log + index tables (crash-consistency).
            let _ = write_txn.open_table(tables::COMMIT_LOG)?;
            let _ = write_txn.open_table(tables::IDX_RECEIPT_BY_HASH)?;
            let _ = write_txn.open_table(tables::IDX_TURN_BY_HASH)?;
            let _ = write_txn.open_table(tables::IDX_TURN_BY_HEIGHT_CREATOR)?;
            let _ = write_txn.open_table(tables::IDX_CELL_BY_ID)?;
            let _ = write_txn.open_table(tables::PER_CELL_RECEIPT_HEAD_BASELINE_V1)?;
            let _ = write_txn.open_table(tables::PER_CELL_RECEIPT_HEAD_CURRENT_V1)?;
            let _ = write_txn.open_table(tables::PROMISE_RESOLUTION_RECORDS_V1)?;
            let _ = write_txn.open_table(tables::PROMISE_RESOLUTION_BATCHES_V1)?;
            let _ = write_txn.open_table(tables::POA_SIGNAL_HEADS_V1)?;
            let _ = write_txn.open_table(tables::POA_SIGNAL_TRANSITIONS_V1)?;
            let _ = write_txn.open_table(tables::POA_SIGNAL_BY_COMMIT_ORDINAL_V1)?;
            poa_event_store::initialize_poa_event_tables_in(&write_txn)?;
            poa_event_batch_v2::initialize_poa_event_batch_tables_v2_in(&write_txn)?;
            poa_holding_consumption::initialize_poa_holding_consumption_tables_in(&write_txn)?;
            poa_compact_authority::initialize_poa_compact_authority_tables_v1_in(&write_txn)?;
            poa_world_activation::initialize_poa_world_activation_tables_v1_in(&write_txn)?;
            poa_activated_content::initialize_poa_activated_content_tables_v1_in(&write_txn)?;
            poa_signal_slot::initialize_poa_signal_slot_tables_v1_in(&write_txn)?;
            poa_signal_session::initialize_poa_signal_session_tables_v1_in(&write_txn)?;
            let _ = write_txn.open_table(tables::PRIVATE_DEPENDENT_TURNS_V1)?;
            let _ = write_txn.open_table(tables::PRIVATE_DEPENDENT_INGRESS_RESERVATIONS_V1)?;
            // Compacted turn block-ids (the no-double-apply carrier for
            // commit-log compaction: ids of applied turns whose records were
            // compacted under a covering checkpoint — `compact_below`).
            let _ = write_txn.open_table(tables::COMMIT_COMPACTED_BLOCK_IDS)?;
            // Forever-digest sets (restart-durable anti-replay carriers).
            let _ = write_txn.open_table(tables::FOREVER_DIGESTS)?;
            // Durable channel rosters (member→seal-pk content; the cell holds
            // only the commitment — .docs-history-noclaude/PERSISTENCE.md §3 roster caveat).
            let _ = write_txn.open_table(tables::CHANNEL_ROSTERS)?;
            // Metadata tables.
            let _ = write_txn.open_table(tables::METADATA)?;
            let _ = write_txn.open_table(tables::METADATA_BYTES)?;
        }
        write_txn.commit()?;
        Ok(())
    }

    /// Compact the database file, reclaiming unused space.
    pub fn compact(&mut self) -> Result<bool> {
        self.db
            .compact()
            .map_err(|e| StoreError::Database(e.to_string()))
    }

    /// Persist a caller-serialized witnessed receipt artifact vector.
    ///
    /// The node owns the typed `WitnessedReceipt` encoding; this crate stores the
    /// bytes under receipt hash so it can stay independent of `dregg-turn`.
    pub fn store_witnessed_receipts_raw(
        &self,
        receipt_hash: &[u8; 32],
        encoded: &[u8],
    ) -> Result<()> {
        let write_txn = self.db.begin_write()?;
        {
            let mut table = write_txn.open_table(tables::WITNESSED_RECEIPTS)?;
            table.insert(receipt_hash, encoded)?;
        }
        write_txn.commit()?;
        Ok(())
    }

    /// Remove a persisted witnessed receipt artifact vector.
    pub fn remove_witnessed_receipts_raw(&self, receipt_hash: &[u8; 32]) -> Result<()> {
        let write_txn = self.db.begin_write()?;
        {
            let mut table = write_txn.open_table(tables::WITNESSED_RECEIPTS)?;
            table.remove(receipt_hash)?;
        }
        write_txn.commit()?;
        Ok(())
    }

    /// Load every persisted witness artifact vector in key order.
    pub fn load_witnessed_receipts_raw(&self) -> Result<Vec<([u8; 32], Vec<u8>)>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::WITNESSED_RECEIPTS)?;
        let mut out = Vec::new();
        for entry in table.iter()? {
            let (key, value) =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            out.push((*key.value(), value.value().to_vec()));
        }
        Ok(out)
    }

    // =========================================================================
    // Durable receipt chain (the served /api/receipts* log + MMR source)
    // =========================================================================

    /// Durably append the caller-serialized `TurnReceipt` at its dense chain
    /// index. An existing byte-identical entry is an idempotent success; an
    /// overwrite, gap, or pre-existing gap is an integrity error.
    pub fn append_receipt_chain_entry(&self, index: u64, encoded: &[u8]) -> Result<()> {
        let write_txn = self.db.begin_write()?;
        Self::write_receipt_chain_entry_in(&write_txn, index, encoded, true)?;
        write_txn.commit()?;
        Ok(())
    }

    /// Validate and optionally append one receipt-log entry inside a caller-owned
    /// write transaction. `allow_insert = false` is the idempotent-replay check:
    /// the exact bytes must already exist at `index`.
    pub(crate) fn write_receipt_chain_entry_in(
        write_txn: &redb::WriteTransaction,
        index: u64,
        encoded: &[u8],
        allow_insert: bool,
    ) -> Result<()> {
        let mut table = write_txn.open_table(tables::RECEIPT_CHAIN)?;
        // For a u64-keyed table, `len = n` and `max_key = n - 1` implies the
        // key set is exactly 0..n: there are n distinct non-negative integers
        // and only n available positions below that maximum. This is the same
        // density proof as a full scan, without turning every append into O(n).
        let expected = {
            let count = table.len()?;
            match (count, table.last()?) {
                (0, None) => 0,
                (0, Some((key, _))) => {
                    return Err(StoreError::Integrity(format!(
                        "receipt log has key {} but reports zero entries",
                        key.value()
                    )));
                }
                (count, Some((key, _))) if key.value() == count - 1 => count,
                (count, Some((key, _))) => {
                    return Err(StoreError::Integrity(format!(
                        "receipt log is not dense: {count} entries but highest index is {}",
                        key.value()
                    )));
                }
                (count, None) => {
                    return Err(StoreError::Integrity(format!(
                        "receipt log reports {count} entries but has no last key"
                    )));
                }
            }
        };

        if index < expected {
            let existing = table.get(index)?.ok_or_else(|| {
                StoreError::Integrity(format!(
                    "receipt log index {index} is below length {expected} but missing"
                ))
            })?;
            if existing.value() != encoded {
                return Err(StoreError::Integrity(format!(
                    "receipt log index {index} already contains different bytes"
                )));
            }
            return Ok(());
        }
        if index != expected {
            return Err(StoreError::Integrity(format!(
                "receipt log append would create a gap: next index {expected}, supplied {index}"
            )));
        }
        if !allow_insert {
            return Err(StoreError::Integrity(format!(
                "finalized-turn replay is missing durable receipt log index {index}"
            )));
        }
        table.insert(index, encoded)?;
        // Once exact-v3 is activated, its live writer must be able to prove the submitting
        // agent's causal receipt predecessor without rescanning the complete global log.  Keep
        // that derived head in the same transaction as the canonical receipt append.  Boot still
        // performs the full replay and rebuilds this index; it is never a substitute for recovery.
        exact_fnsp_v3_frame_head::stage_receipt_head_on_append_in(write_txn, index, encoded)?;
        Ok(())
    }

    /// Load the complete durable receipt chain. Any non-dense key is an integrity
    /// error: boot must not turn a corrupt tail into an accepted rollback to an
    /// earlier receipt head.
    pub fn load_receipt_chain(&self) -> Result<Vec<Vec<u8>>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::RECEIPT_CHAIN)?;
        let mut out = Vec::new();
        let mut expected: u64 = 0;
        for entry in table.iter()? {
            let (key, value) =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            if key.value() != expected {
                return Err(StoreError::Integrity(format!(
                    "receipt log gap: expected index {expected}, found {}",
                    key.value()
                )));
            }
            out.push(value.value().to_vec());
            expected += 1;
        }
        Ok(out)
    }

    /// Length of the durable receipt chain. A gap is an integrity error, not a
    /// shorter accepted history.
    pub fn receipt_chain_len(&self) -> Result<u64> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::RECEIPT_CHAIN)?;
        let count = table.len()?;
        match (count, table.last()?) {
            (0, None) => Ok(0),
            (0, Some((key, _))) => Err(StoreError::Integrity(format!(
                "receipt log has key {} but reports zero entries",
                key.value()
            ))),
            (count, Some((key, _))) if key.value() == count - 1 => Ok(count),
            (count, Some((key, _))) => Err(StoreError::Integrity(format!(
                "receipt log is not dense: {count} entries but highest index is {}",
                key.value()
            ))),
            (count, None) => Err(StoreError::Integrity(format!(
                "receipt log reports {count} entries but has no last key"
            ))),
        }
    }

    // =========================================================================
    // Durable REALM-substrate op log (realm-model persistence)
    // =========================================================================
    //
    // The durable half of the MUD-SUBSTRATE receipt/turn-chain dependency: an
    // ordered, dense, gap-checked log of admitted realm-model operations. It rides
    // the EXACT density discipline of the receipt chain above — a `RealmWorld` is
    // reconstructed by replaying this log through a fresh world on boot, so a
    // realm/instance/identity/catalog created through the node survives a restart
    // with the identical receipt-chain head.

    /// Durably append the caller-serialized `RealmOp` at its dense log index. An
    /// existing byte-identical entry is an idempotent success; an overwrite, gap,
    /// or pre-existing gap is an integrity error. Same shape as
    /// [`Self::append_receipt_chain_entry`], minus the receipt-index side effect.
    pub fn append_realm_log_entry(&self, index: u64, encoded: &[u8]) -> Result<()> {
        let write_txn = self.db.begin_write()?;
        {
            let mut table = write_txn.open_table(tables::REALM_LOG)?;
            let expected = {
                let count = table.len()?;
                match (count, table.last()?) {
                    (0, None) => 0,
                    (0, Some((key, _))) => {
                        return Err(StoreError::Integrity(format!(
                            "realm log has key {} but reports zero entries",
                            key.value()
                        )));
                    }
                    (count, Some((key, _))) if key.value() == count - 1 => count,
                    (count, Some((key, _))) => {
                        return Err(StoreError::Integrity(format!(
                            "realm log is not dense: {count} entries but highest index is {}",
                            key.value()
                        )));
                    }
                    (count, None) => {
                        return Err(StoreError::Integrity(format!(
                            "realm log reports {count} entries but has no last key"
                        )));
                    }
                }
            };
            if index < expected {
                let existing = table.get(index)?.ok_or_else(|| {
                    StoreError::Integrity(format!(
                        "realm log index {index} is below length {expected} but missing"
                    ))
                })?;
                if existing.value() != encoded {
                    return Err(StoreError::Integrity(format!(
                        "realm log index {index} already contains different bytes"
                    )));
                }
                return Ok(());
            }
            if index != expected {
                return Err(StoreError::Integrity(format!(
                    "realm log append would create a gap: next index {expected}, supplied {index}"
                )));
            }
            table.insert(index, encoded)?;
        }
        write_txn.commit()?;
        Ok(())
    }

    /// Load the complete durable realm op log. Any non-dense key is an integrity
    /// error: boot must not turn a corrupt tail into an accepted rollback to an
    /// earlier realm head.
    pub fn load_realm_log(&self) -> Result<Vec<Vec<u8>>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::REALM_LOG)?;
        let mut out = Vec::new();
        let mut expected: u64 = 0;
        for entry in table.iter()? {
            let (key, value) =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            if key.value() != expected {
                return Err(StoreError::Integrity(format!(
                    "realm log gap: expected index {expected}, found {}",
                    key.value()
                )));
            }
            out.push(value.value().to_vec());
            expected += 1;
        }
        Ok(out)
    }

    /// Length of the durable realm op log. A gap is an integrity error, not a
    /// shorter accepted history.
    pub fn realm_log_len(&self) -> Result<u64> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::REALM_LOG)?;
        let count = table.len()?;
        match (count, table.last()?) {
            (0, None) => Ok(0),
            (0, Some((key, _))) => Err(StoreError::Integrity(format!(
                "realm log has key {} but reports zero entries",
                key.value()
            ))),
            (count, Some((key, _))) if key.value() == count - 1 => Ok(count),
            (count, Some((key, _))) => Err(StoreError::Integrity(format!(
                "realm log is not dense: {count} entries but highest index is {}",
                key.value()
            ))),
            (count, None) => Err(StoreError::Integrity(format!(
                "realm log reports {count} entries but has no last key"
            ))),
        }
    }

    // =========================================================================
    // Durable receipt-index head anchor (finding F5)
    // =========================================================================
    //
    // The served `/api/receipts/index/*` non-omission MMR is rebuilt from the
    // receipt chain on boot. This compact `{ len, root }` anchor lets recovery
    // DETECT a chain that no longer reproduces the head served before the
    // restart (a store-integrity event on an ADDITIVE, non-commit-gating index),
    // survives restart as a checked value, and is the durable head a future
    // retention-windowed log compaction must preserve. It is O(1) on disk — it
    // never persists the leaf set — so bounding the receipt/realm-log DISK and
    // the O(n) boot replay of the full served chain remains a scoped follow-up
    // (F5-b): the served chain must stay fully in memory to answer range
    // openings, and the Lean-mirrored `MMR.lean` structure would need a
    // compacted-prefix extension to keep serving the full-history root.

    /// Durably record the served receipt-index head `{ len, root }` (40 bytes:
    /// little-endian `len` ‖ `root`). Idempotent overwrite.
    pub fn persist_receipt_index_head(&self, len: u64, root: &[u8; 32]) -> Result<()> {
        let mut buf = [0u8; 40];
        buf[..8].copy_from_slice(&len.to_le_bytes());
        buf[8..].copy_from_slice(root);
        let write_txn = self.db.begin_write()?;
        {
            let mut table = write_txn.open_table(tables::METADATA_BYTES)?;
            table.insert(tables::META_RECEIPT_INDEX_HEAD, buf.as_slice())?;
        }
        write_txn.commit()?;
        Ok(())
    }

    /// Load the durable receipt-index head anchor, or `None` if never recorded
    /// (a fresh node, or one that has not yet served the index).
    pub fn load_receipt_index_head(&self) -> Result<Option<(u64, [u8; 32])>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::METADATA_BYTES)?;
        let Some(guard) = table.get(tables::META_RECEIPT_INDEX_HEAD)? else {
            return Ok(None);
        };
        let bytes = guard.value();
        if bytes.len() != 40 {
            return Err(StoreError::Integrity(format!(
                "receipt-index head anchor is {} bytes, expected 40",
                bytes.len()
            )));
        }
        let mut len_bytes = [0u8; 8];
        len_bytes.copy_from_slice(&bytes[..8]);
        let mut root = [0u8; 32];
        root.copy_from_slice(&bytes[8..]);
        Ok(Some((u64::from_le_bytes(len_bytes), root)))
    }

    // =========================================================================
    // Note Tree Storage
    // =========================================================================

    /// Store a note commitment at the next position. Returns the position assigned.
    ///
    /// Invalidates the cached note tree root so the next call to `note_tree_root()`
    /// will recompute from the updated tree.
    pub fn store_note_commitment(
        &self,
        commitment: &dregg_cell::note::NoteCommitment,
    ) -> Result<u64> {
        let write_txn = self.db.begin_write()?;
        let position;
        {
            let mut meta = write_txn.open_table(tables::METADATA)?;
            let current_size = meta
                .get(tables::META_NOTE_TREE_SIZE)?
                .map(|g| g.value())
                .unwrap_or(0);
            position = current_size;

            let mut table = write_txn.open_table(tables::NOTE_COMMITMENTS)?;
            table.insert(position, &commitment.0)?;

            meta.insert(tables::META_NOTE_TREE_SIZE, position + 1)?;

            // Invalidate the cached root within the same transaction.
            let mut meta_bytes = write_txn.open_table(tables::METADATA_BYTES)?;
            meta_bytes.remove(tables::META_NOTE_TREE_ROOT_CACHE)?;
        }
        write_txn.commit()?;
        Ok(position)
    }

    /// Store a nullifier (mark a note as spent).
    ///
    /// Returns Ok(()) if the nullifier was newly added, or an integrity error
    /// if it was already present (double-spend).
    pub fn store_nullifier(&self, nullifier: &dregg_cell::note::Nullifier) -> Result<()> {
        let write_txn = self.db.begin_write()?;
        {
            let mut table = write_txn.open_table(tables::NULLIFIERS)?;
            if table.get(&nullifier.0)?.is_some() {
                return Err(StoreError::Integrity(
                    "nullifier already spent (double-spend)".to_string(),
                ));
            }
            table.insert(&nullifier.0, ())?;
        }
        write_txn.commit()?;
        Ok(())
    }

    /// Check whether a nullifier has been spent (is in the set).
    pub fn is_nullifier_spent(&self, nullifier: &dregg_cell::note::Nullifier) -> Result<bool> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::NULLIFIERS)?;
        Ok(table.get(&nullifier.0)?.is_some())
    }

    /// Get the current note tree root.
    ///
    /// Returns the cached root if available (O(1) read from metadata). Falls back
    /// to full tree reconstruction only if the cache is missing (e.g., first call
    /// on a database created before the cache was introduced, or after corruption
    /// recovery).
    ///
    /// On cache miss, a write transaction is used to atomically read the current
    /// commitments and write the computed root, preventing TOCTOU races where
    /// another writer could append a commitment between the read and the cache write.
    pub fn note_tree_root(&self) -> Result<[u8; 32]> {
        // Try to read the cached root first (fast path).
        let read_txn = self.db.begin_read()?;
        let meta_bytes = read_txn.open_table(tables::METADATA_BYTES)?;
        if let Some(guard) = meta_bytes.get(tables::META_NOTE_TREE_ROOT_CACHE)? {
            let cached = guard.value();
            if cached.len() == 32 {
                let mut root = [0u8; 32];
                root.copy_from_slice(cached);
                return Ok(root);
            }
        }
        drop(meta_bytes);
        drop(read_txn);

        // Cache miss: use a write transaction to atomically read commitments and
        // persist the computed root. This prevents a TOCTOU race where another
        // writer could append between our read and the cache write.
        let write_txn = self.db.begin_write()?;

        // Re-check the cache under the write lock (another thread may have
        // populated it while we were waiting for the write transaction).
        let cached_root = {
            let meta_bytes_table = write_txn.open_table(tables::METADATA_BYTES)?;
            let maybe_cached = meta_bytes_table.get(tables::META_NOTE_TREE_ROOT_CACHE)?;
            match maybe_cached {
                Some(guard) => {
                    let cached = guard.value();
                    if cached.len() == 32 {
                        let mut r = [0u8; 32];
                        r.copy_from_slice(cached);
                        Some(r)
                    } else {
                        None
                    }
                }
                None => None,
            }
        };

        if let Some(r) = cached_root {
            // No changes to commit; just abort the write transaction and return.
            return Ok(r);
        }

        // Read all commitments within this write transaction's snapshot.
        let count = {
            let meta = write_txn.open_table(tables::METADATA)?;
            meta.get(tables::META_NOTE_TREE_SIZE)?
                .map(|g| g.value())
                .unwrap_or(0)
        };

        let mut commitments = Vec::with_capacity(count as usize);
        {
            let commitment_table = write_txn.open_table(tables::NOTE_COMMITMENTS)?;
            for pos in 0..count {
                match commitment_table.get(pos)? {
                    Some(guard) => {
                        commitments.push(dregg_cell::note::NoteCommitment(*guard.value()));
                    }
                    None => {
                        return Err(StoreError::Integrity(format!(
                            "missing note commitment at position {pos}"
                        )));
                    }
                }
            }
        }

        let mut tree = note_tree::NoteTree::from_commitments(commitments);
        let root = tree.root();

        // Persist the computed root.
        {
            let mut meta_bytes_w = write_txn.open_table(tables::METADATA_BYTES)?;
            meta_bytes_w.insert(tables::META_NOTE_TREE_ROOT_CACHE, root.as_slice())?;
        }
        write_txn.commit()?;

        Ok(root)
    }

    /// Get the number of note commitments stored.
    pub fn note_count(&self) -> Result<u64> {
        let read_txn = self.db.begin_read()?;
        let meta = read_txn.open_table(tables::METADATA)?;
        Ok(meta
            .get(tables::META_NOTE_TREE_SIZE)?
            .map(|g| g.value())
            .unwrap_or(0))
    }

    /// Load all note commitments in order (for tree reconstruction).
    pub fn load_all_note_commitments(&self) -> Result<Vec<dregg_cell::note::NoteCommitment>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::NOTE_COMMITMENTS)?;
        let meta = read_txn.open_table(tables::METADATA)?;

        let count = meta
            .get(tables::META_NOTE_TREE_SIZE)?
            .map(|g| g.value())
            .unwrap_or(0);

        let mut commitments = Vec::with_capacity(count as usize);
        for pos in 0..count {
            match table.get(pos)? {
                Some(guard) => {
                    commitments.push(dregg_cell::note::NoteCommitment(*guard.value()));
                }
                None => {
                    return Err(StoreError::Integrity(format!(
                        "missing note commitment at position {pos}"
                    )));
                }
            }
        }
        Ok(commitments)
    }

    /// Load all nullifiers from persistent storage.
    pub fn load_all_nullifiers(&self) -> Result<Vec<dregg_cell::note::Nullifier>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::NULLIFIERS)?;

        let mut nullifiers = Vec::new();
        let iter = table.iter()?;
        for entry in iter {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            nullifiers.push(dregg_cell::note::Nullifier(*entry.0.value()));
        }
        Ok(nullifiers)
    }

    /// Load the complete circuit-facing nullifier accumulator record.
    ///
    /// Unlike [`Self::load_all_nullifiers`], this retains the public spent-note
    /// value and canonical append sequence needed to reconstruct the same
    /// eight-felt accumulator after restart. A nonempty legacy presence table
    /// without these additive rows is refused rather than guessed.
    pub fn load_faithful_nullifier_records(
        &self,
    ) -> Result<Vec<(dregg_cell::note::Nullifier, u64, u64)>> {
        let read_txn = self.db.begin_read()?;
        let presence = read_txn.open_table(tables::NULLIFIERS)?;
        let records = read_txn.open_table(tables::NULLIFIER_RECORDS_V1)?;
        let presence_len = presence.len()?;
        let records_len = records.len()?;
        if presence_len != records_len {
            return Err(StoreError::Integrity(format!(
                "nullifier presence/record table lengths disagree ({presence_len} != {records_len}); \
                 legacy nonempty images require an explicit value/sequence migration"
            )));
        }

        let capacity = usize::try_from(records_len).map_err(|_| {
            StoreError::Integrity("nullifier record count does not fit usize".to_string())
        })?;
        let mut out = Vec::with_capacity(capacity);
        let mut seen_seq = vec![false; capacity];
        for entry in records.iter()? {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            let nullifier = *entry.0.value();
            if presence.get(&nullifier)?.is_none() {
                return Err(StoreError::Integrity(
                    "nullifier record has no matching spent-presence row".to_string(),
                ));
            }
            let bytes = entry.1.value();
            let mut value = [0u8; 8];
            value.copy_from_slice(&bytes[..8]);
            let mut seq = [0u8; 8];
            seq.copy_from_slice(&bytes[8..]);
            let value = u64::from_le_bytes(value);
            let seq = u64::from_le_bytes(seq);
            let seq_index = usize::try_from(seq).map_err(|_| {
                StoreError::Integrity("nullifier append sequence does not fit usize".to_string())
            })?;
            if seq_index >= capacity || seen_seq[seq_index] {
                return Err(StoreError::Integrity(
                    "nullifier append sequence is duplicated or outside the dense durable range"
                        .to_string(),
                ));
            }
            seen_seq[seq_index] = true;
            out.push((dregg_cell::note::Nullifier(nullifier), value, seq));
        }
        if seen_seq.iter().any(|seen| !seen) {
            return Err(StoreError::Integrity(
                "nullifier append sequence has a durable gap".to_string(),
            ));
        }
        out.sort_by_key(|(nullifier, _, seq)| (*seq, *nullifier));
        Ok(out)
    }

    /// Return the exact durable faithful-nullifier row count without decoding
    /// the full accumulator.  The legacy presence table must have the same
    /// cardinality; disagreement is an integrity failure, never a cache key.
    pub fn faithful_nullifier_record_count(&self) -> Result<u64> {
        let read_txn = self.db.begin_read()?;
        let presence = read_txn.open_table(tables::NULLIFIERS)?;
        let records = read_txn.open_table(tables::NULLIFIER_RECORDS_V1)?;
        let presence_len = presence.len()?;
        let records_len = records.len()?;
        if presence_len != records_len {
            return Err(StoreError::Integrity(format!(
                "nullifier presence/record table lengths disagree ({presence_len} != {records_len}); \
                 legacy nonempty images require an explicit value/sequence migration"
            )));
        }
        Ok(records_len)
    }

    /// Exact durable eight-felt nullifier-accumulator root used by live root
    /// attestation. This is separate from [`Self::nullifier_set_root`], the
    /// legacy BLAKE3 key-only non-membership tree.
    pub fn faithful_nullifier_root(&self) -> Result<[u8; 32]> {
        let records = self.load_faithful_nullifier_records()?;
        let set = dregg_cell::nullifier_set::NullifierSet::from_records(records).map_err(|e| {
            StoreError::Integrity(format!(
                "durable nullifier accumulator cannot be reconstructed: {e}"
            ))
        })?;
        Ok(set.root8().to_bytes32())
    }

    /// Compute, without mutating the store, the nullifier root that must be
    /// attested if `spends` are atomically appended to the current durable set.
    pub fn plan_faithful_nullifier_successor(
        &self,
        spends: &[commit_log::FinalizedNullifierRecord],
    ) -> Result<[u8; 32]> {
        let records = self.load_faithful_nullifier_records()?;
        let mut set =
            dregg_cell::nullifier_set::NullifierSet::from_records(records).map_err(|e| {
                StoreError::Integrity(format!(
                    "durable nullifier accumulator cannot be reconstructed: {e}"
                ))
            })?;
        for spend in spends {
            set.insert(dregg_cell::note::Nullifier(spend.nullifier), spend.value)
                .map_err(|_| {
                    StoreError::Integrity(
                        "nullifier already spent or duplicated within finalized turn".to_string(),
                    )
                })?;
        }
        Ok(set.root8().to_bytes32())
    }

    /// Compute the nullifier set root from all stored nullifiers.
    pub fn nullifier_set_root(&self) -> Result<[u8; 32]> {
        let nullifiers = self.load_all_nullifiers()?;
        let set = note_tree::PersistentNullifierSet::from_nullifiers(nullifiers);
        Ok(set.root())
    }

    // =========================================================================
    // Generic Config Storage (METADATA_BYTES)
    // =========================================================================

    /// Test-only: arm/disarm the [`Self::get_config`] / [`Self::set_config`] fault
    /// seam. Never called in production — an API durability test sets it to drive
    /// a caller's fail-closed refusal (e.g. `/api/discharge` refusing to serve on
    /// an unknown replay set), then clears it to prove the honest path still works.
    #[doc(hidden)]
    pub fn set_fail_config_io(&self, fail: bool) {
        self.fail_config_io
            .store(fail, std::sync::atomic::Ordering::Relaxed);
    }

    fn config_io_fault(&self) -> Option<StoreError> {
        self.fail_config_io
            .load(std::sync::atomic::Ordering::Relaxed)
            .then(|| {
                StoreError::Database(
                    "config io fault injected (test-only fail_config_io seam)".to_string(),
                )
            })
    }

    /// Store a byte blob under a config key.
    pub fn set_config(&self, key: &str, value: &[u8]) -> Result<()> {
        self.set_config_batch(&[(key, value)])
    }

    /// Store related config blobs in one transaction. No prefix of this batch
    /// becomes visible if an insertion fails before commit.
    /// A commit error still requires the caller to recover its durable state.
    pub fn set_config_batch(&self, entries: &[(&str, &[u8])]) -> Result<()> {
        if let Some(fault) = self.config_io_fault() {
            return Err(fault);
        }
        #[cfg(test)]
        let fail_after = FAIL_CONFIG_BATCH_AFTER.with(|fault| fault.take());
        let write_txn = self.db.begin_write()?;
        {
            let mut table = write_txn.open_table(tables::METADATA_BYTES)?;
            for (index, (key, value)) in entries.iter().enumerate() {
                table.insert(*key, *value)?;
                #[cfg(test)]
                if fail_after == Some(index + 1) {
                    return Err(StoreError::Database(
                        "config batch failure injected after insert".to_string(),
                    ));
                }
                #[cfg(not(test))]
                let _ = index;
            }
        }
        write_txn.commit()?;
        Ok(())
    }

    /// Load a byte blob stored under a config key.
    pub fn get_config(&self, key: &str) -> Result<Option<Vec<u8>>> {
        if let Some(fault) = self.config_io_fault() {
            return Err(fault);
        }
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::METADATA_BYTES)?;
        match table.get(key)? {
            Some(guard) => Ok(Some(guard.value().to_vec())),
            None => Ok(None),
        }
    }

    // =========================================================================
    // Proof Hash Nullifier Storage (for conditional turn replay prevention)
    // =========================================================================

    /// Store a proof hash (used in conditional turn resolution) to prevent replay.
    ///
    /// Returns Ok(true) if newly inserted, Ok(false) if already present.
    ///
    /// The check-and-insert is performed atomically within a single write
    /// transaction to prevent TOCTOU races where two concurrent calls could
    /// both pass the existence check.
    pub fn insert_proof_hash(&self, hash: &[u8; 32]) -> Result<bool> {
        // We reuse METADATA_BYTES with a "proof_hash:" prefix key.
        let key = format!("proof_hash:{}", hex_encode_bytes(hash));
        let write_txn = self.db.begin_write()?;
        {
            let mut table = write_txn.open_table(tables::METADATA_BYTES)?;
            if table.get(key.as_str())?.is_some() {
                return Ok(false);
            }
            table.insert(key.as_str(), &[1u8] as &[u8])?;
        }
        write_txn.commit()?;
        Ok(true)
    }

    /// Store a proof hash with an associated block height for TTL-based eviction.
    ///
    /// Returns Ok(true) if newly inserted, Ok(false) if already present.
    pub fn insert_proof_hash_with_height(&self, hash: &[u8; 32], height: u64) -> Result<bool> {
        let key = format!("proof_hash:{}", hex_encode_bytes(hash));
        let write_txn = self.db.begin_write()?;
        {
            let mut table = write_txn.open_table(tables::METADATA_BYTES)?;
            if table.get(key.as_str())?.is_some() {
                return Ok(false);
            }
            // Store the height as 8-byte LE value for later pruning.
            table.insert(key.as_str(), &height.to_le_bytes() as &[u8])?;
        }
        write_txn.commit()?;
        Ok(true)
    }

    /// Prune proof hashes older than `max_age` blocks from the current height.
    ///
    /// Entries stored without a height (legacy 1-byte value) are left intact.
    /// Returns the number of entries pruned.
    pub fn prune_old_proof_hashes(&self, current_height: u64, max_age: u64) -> Result<u64> {
        let min_height = current_height.saturating_sub(max_age);
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::METADATA_BYTES)?;

        let prefix = "proof_hash:";
        let mut keys_to_remove = Vec::new();

        let range = table.range(prefix..)?;
        for entry in range {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            let key = entry.0.value();
            if !key.starts_with(prefix) {
                break;
            }
            let value = entry.1.value();
            // Only prune entries that have height data (8 bytes).
            if value.len() == 8 {
                let stored_height = u64::from_le_bytes(value.try_into().unwrap());
                if stored_height < min_height {
                    keys_to_remove.push(key.to_string());
                }
            }
        }
        drop(table);
        drop(read_txn);

        if keys_to_remove.is_empty() {
            return Ok(0);
        }

        let count = keys_to_remove.len() as u64;
        let write_txn = self.db.begin_write()?;
        {
            let mut table = write_txn.open_table(tables::METADATA_BYTES)?;
            for key in &keys_to_remove {
                table.remove(key.as_str())?;
            }
        }
        write_txn.commit()?;
        Ok(count)
    }

    /// Load all stored proof hashes (for populating the in-memory set on startup).
    pub fn load_all_proof_hashes(&self) -> Result<std::collections::HashSet<[u8; 32]>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::METADATA_BYTES)?;
        let mut hashes = std::collections::HashSet::new();

        let prefix = "proof_hash:";
        let range = table.range(prefix..)?;
        for entry in range {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            let key = entry.0.value();
            if !key.starts_with(prefix) {
                break;
            }
            // Parse the hex suffix back to [u8; 32].
            let hex_part = &key[prefix.len()..];
            if hex_part.len() == 64
                && let Ok(bytes) = hex_decode_bytes(hex_part)
            {
                hashes.insert(bytes);
            }
        }
        Ok(hashes)
    }

    /// Atomically spend a note: insert the nullifier and store the new commitment
    /// in a single transaction.
    ///
    /// This prevents the case where a nullifier is recorded but the new commitment
    /// is lost (or vice versa) due to a crash between two separate transactions.
    ///
    /// Returns the position of the new commitment in the note tree.
    /// Returns an integrity error if the nullifier was already spent (double-spend).
    pub fn spend_note_atomic(
        &self,
        nullifier: &dregg_cell::note::Nullifier,
        new_commitment: &dregg_cell::note::NoteCommitment,
    ) -> Result<u64> {
        let write_txn = self.db.begin_write()?;
        let position;
        {
            // Check and insert nullifier.
            let mut nullifier_table = write_txn.open_table(tables::NULLIFIERS)?;
            if nullifier_table.get(&nullifier.0)?.is_some() {
                return Err(StoreError::Integrity(
                    "nullifier already spent (double-spend)".to_string(),
                ));
            }
            nullifier_table.insert(&nullifier.0, ())?;

            // Insert new commitment at the next position.
            let mut meta = write_txn.open_table(tables::METADATA)?;
            let current_size = meta
                .get(tables::META_NOTE_TREE_SIZE)?
                .map(|g| g.value())
                .unwrap_or(0);
            position = current_size;

            let mut commitment_table = write_txn.open_table(tables::NOTE_COMMITMENTS)?;
            commitment_table.insert(position, &new_commitment.0)?;

            meta.insert(tables::META_NOTE_TREE_SIZE, position + 1)?;

            // Invalidate the cached note tree root.
            let mut meta_bytes = write_txn.open_table(tables::METADATA_BYTES)?;
            meta_bytes.remove(tables::META_NOTE_TREE_ROOT_CACHE)?;
        }
        write_txn.commit()?;
        Ok(position)
    }
}

// =============================================================================
// Internal hex helpers
// =============================================================================

fn hex_encode_bytes(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn hex_decode_bytes(s: &str) -> std::result::Result<[u8; 32], ()> {
    if s.len() != 64 {
        return Err(());
    }
    let mut out = [0u8; 32];
    for (i, chunk) in s.as_bytes().chunks(2).enumerate() {
        let high = hex_nibble(chunk[0]).ok_or(())?;
        let low = hex_nibble(chunk[1]).ok_or(())?;
        out[i] = (high << 4) | low;
    }
    Ok(out)
}

fn hex_nibble(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b - b'0'),
        b'a'..=b'f' => Some(b - b'a' + 10),
        b'A'..=b'F' => Some(b - b'A' + 10),
        _ => None,
    }
}
