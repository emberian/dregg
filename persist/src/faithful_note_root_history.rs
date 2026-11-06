//! Versioned, authenticated history for faithful-eight note-tree roots.
//!
//! `Dregg2.Circuit.CommitmentTreeWideHistory` is the semantic authority.  This
//! module is its strict Rust interpreter and durable carrier.  Every v1 record
//! binds one exact history edge:
//!
//! * session, federation, and committee epoch;
//! * predecessor and successor faithful-eight roots;
//! * predecessor and successor note counts;
//! * consecutive finalized heights and the carrying block id.
//!
//! The signed message is the record's fixed-width canonical `FNHR` encoding.
//! The production verifier is the enrolled-roster hybrid quorum verifier
//! (Ed25519 AND ML-DSA-65).  Structural validity is not called authentication.
//!
//! The finalized-turn store path can append one of these records in the same
//! redb transaction as the exact note leaves, receipt, attested root, and commit
//! cursor.  The existing scalar note-tree read APIs remain intact while their
//! wire consumers rotate.  Note-spend membership, nullifier, and conservation
//! authorization are separate cuts: this history authenticates the append-only
//! commitment frontier; it does not manufacture those proofs.

use redb::{ReadableTable, ReadableTableMetadata};
use serde::{Deserialize, Serialize};

use dregg_circuit::Faithful8;
use dregg_circuit::field::BABYBEAR_P;
use dregg_federation::frost::MlDsaPublicKey;
use dregg_types::{HybridQuorumSig, PublicKey};

use crate::{PersistentStore, Result as StoreResult, StoreError, tables};

const RECORD_MAGIC: [u8; 4] = *b"FNHR";
const ANCHOR_MAGIC: [u8; 4] = *b"FNHA";
const HEAD_MAGIC: [u8; 4] = *b"FNHH";
const VERSION_V1: u16 = 1;
const RESERVED_ZERO: u16 = 0;

/// `magic(4) || version(2) || reserved(2) || session(32) || federation(32) ||
/// epoch(8) || previous_height(8) || height(8) || previous_count(8) ||
/// count(8) || predecessor(32) || successor(32) || block_id(32)`.
pub const FAITHFUL_NOTE_ROOT_RECORD_V1_BYTES: usize = 208;
/// Fixed-width anchor encoding.
pub const FAITHFUL_NOTE_ROOT_ANCHOR_V1_BYTES: usize = 128;
/// Fixed-width persisted head seal: anchor bytes plus the exact record count.
pub const FAITHFUL_NOTE_ROOT_HEAD_V1_BYTES: usize = 136;

/// Bound hostile-allocation surface for a quorum envelope.  A normal hybrid
/// quorum is far below this, even with ML-DSA signatures.
const MAX_ENVELOPE_BYTES: usize = 4 * 1024 * 1024;
const MAX_QUORUM_SIGNERS: usize = 512;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FaithfulNoteRootHistoryError {
    Malformed(&'static str),
    NonCanonicalRoot { lane: usize, value: u32 },
    ContextMismatch(&'static str),
    NonConsecutiveHeight,
    CountRegression,
    RootDidNotTrackCount,
    Replay,
    Fork,
    DuplicateBlock,
    AuthenticationFailed,
    SnapshotMismatch(&'static str),
}

impl std::fmt::Display for FaithfulNoteRootHistoryError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Malformed(what) => write!(f, "malformed faithful note-root {what}"),
            Self::NonCanonicalRoot { lane, value } => {
                write!(f, "non-canonical faithful note-root lane {lane}: {value}")
            }
            Self::ContextMismatch(what) => write!(f, "faithful note-root {what} mismatch"),
            Self::NonConsecutiveHeight => {
                write!(f, "faithful note-root height is not the exact successor")
            }
            Self::CountRegression => write!(f, "faithful note-root note count regressed"),
            Self::RootDidNotTrackCount => {
                write!(f, "faithful note-root/count transition is inconsistent")
            }
            Self::Replay => write!(f, "faithful note-root record replay"),
            Self::Fork => write!(f, "faithful note-root history fork"),
            Self::DuplicateBlock => write!(f, "faithful note-root block replay"),
            Self::AuthenticationFailed => {
                write!(f, "faithful note-root hybrid authentication failed")
            }
            Self::SnapshotMismatch(what) => {
                write!(f, "faithful note-root snapshot {what} mismatch")
            }
        }
    }
}

impl std::error::Error for FaithfulNoteRootHistoryError {}

fn integrity(error: FaithfulNoteRootHistoryError) -> StoreError {
    StoreError::Integrity(error.to_string())
}

fn nonzero(bytes: &[u8; 32]) -> bool {
    bytes.iter().any(|byte| *byte != 0)
}

/// Canonical byte packing of a genuine eight-lane BabyBear root.
///
/// The private field prevents an arbitrary 32-byte string from being read as a
/// wide root.  Every 4-byte little-endian lane must be `< p`; malformed lanes
/// such as `p`, trailing bytes, or a short record refuse before authentication.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CanonicalFaithfulRoot([u8; 32]);

impl CanonicalFaithfulRoot {
    pub fn from_faithful(root: Faithful8) -> Self {
        Self(root.to_bytes32())
    }

    pub fn from_bytes(bytes: [u8; 32]) -> std::result::Result<Self, FaithfulNoteRootHistoryError> {
        for (lane, chunk) in bytes.chunks_exact(4).enumerate() {
            let value = u32::from_le_bytes(chunk.try_into().expect("four-byte lane"));
            if value >= BABYBEAR_P {
                return Err(FaithfulNoteRootHistoryError::NonCanonicalRoot { lane, value });
            }
        }
        Ok(Self(bytes))
    }

    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }

    pub fn to_bytes(self) -> [u8; 32] {
        self.0
    }

    pub fn to_faithful(self) -> Faithful8 {
        // Canonicality was checked on construction, so this roundtrip performs
        // no reduction and returns the exact eight lanes.
        Faithful8::from_bytes32(&self.0)
    }
}

/// Externally trusted start head for one root-history segment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FaithfulNoteRootAnchorV1 {
    pub session_id: [u8; 32],
    pub federation_id: [u8; 32],
    pub committee_epoch: u64,
    pub height: u64,
    pub note_count: u64,
    pub root: CanonicalFaithfulRoot,
}

impl FaithfulNoteRootAnchorV1 {
    pub fn new(
        session_id: [u8; 32],
        federation_id: [u8; 32],
        committee_epoch: u64,
        height: u64,
        note_count: u64,
        root: CanonicalFaithfulRoot,
    ) -> std::result::Result<Self, FaithfulNoteRootHistoryError> {
        if !nonzero(&session_id) {
            return Err(FaithfulNoteRootHistoryError::Malformed("zero session id"));
        }
        if !nonzero(&federation_id) {
            return Err(FaithfulNoteRootHistoryError::Malformed(
                "zero federation id",
            ));
        }
        Ok(Self {
            session_id,
            federation_id,
            committee_epoch,
            height,
            note_count,
            root,
        })
    }

    pub fn to_bytes(&self) -> [u8; FAITHFUL_NOTE_ROOT_ANCHOR_V1_BYTES] {
        let mut out = [0u8; FAITHFUL_NOTE_ROOT_ANCHOR_V1_BYTES];
        out[0..4].copy_from_slice(&ANCHOR_MAGIC);
        out[4..6].copy_from_slice(&VERSION_V1.to_le_bytes());
        out[6..8].copy_from_slice(&RESERVED_ZERO.to_le_bytes());
        out[8..40].copy_from_slice(&self.session_id);
        out[40..72].copy_from_slice(&self.federation_id);
        out[72..80].copy_from_slice(&self.committee_epoch.to_le_bytes());
        out[80..88].copy_from_slice(&self.height.to_le_bytes());
        out[88..96].copy_from_slice(&self.note_count.to_le_bytes());
        out[96..128].copy_from_slice(self.root.as_bytes());
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> std::result::Result<Self, FaithfulNoteRootHistoryError> {
        if bytes.len() != FAITHFUL_NOTE_ROOT_ANCHOR_V1_BYTES {
            return Err(FaithfulNoteRootHistoryError::Malformed("anchor length"));
        }
        if bytes[0..4] != ANCHOR_MAGIC
            || u16::from_le_bytes(bytes[4..6].try_into().unwrap()) != VERSION_V1
            || u16::from_le_bytes(bytes[6..8].try_into().unwrap()) != RESERVED_ZERO
        {
            return Err(FaithfulNoteRootHistoryError::Malformed("anchor header"));
        }
        let session_id = bytes[8..40].try_into().unwrap();
        let federation_id = bytes[40..72].try_into().unwrap();
        let committee_epoch = u64::from_le_bytes(bytes[72..80].try_into().unwrap());
        let height = u64::from_le_bytes(bytes[80..88].try_into().unwrap());
        let note_count = u64::from_le_bytes(bytes[88..96].try_into().unwrap());
        let root = CanonicalFaithfulRoot::from_bytes(bytes[96..128].try_into().unwrap())?;
        Self::new(
            session_id,
            federation_id,
            committee_epoch,
            height,
            note_count,
            root,
        )
    }
}

/// Fixed-width v1 transition.  Construction is validation; a value of this
/// type is canonical and internally well-formed, but not yet authenticated.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FaithfulNoteRootRecordV1 {
    pub session_id: [u8; 32],
    pub federation_id: [u8; 32],
    pub committee_epoch: u64,
    pub previous_height: u64,
    pub height: u64,
    pub previous_note_count: u64,
    pub note_count: u64,
    pub predecessor: CanonicalFaithfulRoot,
    pub successor: CanonicalFaithfulRoot,
    pub block_id: [u8; 32],
}

impl FaithfulNoteRootRecordV1 {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        session_id: [u8; 32],
        federation_id: [u8; 32],
        committee_epoch: u64,
        previous_height: u64,
        height: u64,
        previous_note_count: u64,
        note_count: u64,
        predecessor: CanonicalFaithfulRoot,
        successor: CanonicalFaithfulRoot,
        block_id: [u8; 32],
    ) -> std::result::Result<Self, FaithfulNoteRootHistoryError> {
        if !nonzero(&session_id) {
            return Err(FaithfulNoteRootHistoryError::Malformed("zero session id"));
        }
        if !nonzero(&federation_id) {
            return Err(FaithfulNoteRootHistoryError::Malformed(
                "zero federation id",
            ));
        }
        if !nonzero(&block_id) {
            return Err(FaithfulNoteRootHistoryError::Malformed("zero block id"));
        }
        if previous_height.checked_add(1) != Some(height) {
            return Err(FaithfulNoteRootHistoryError::NonConsecutiveHeight);
        }
        if note_count < previous_note_count {
            return Err(FaithfulNoteRootHistoryError::CountRegression);
        }
        let count_changed = note_count > previous_note_count;
        let root_changed = successor != predecessor;
        if count_changed != root_changed {
            return Err(FaithfulNoteRootHistoryError::RootDidNotTrackCount);
        }
        Ok(Self {
            session_id,
            federation_id,
            committee_epoch,
            previous_height,
            height,
            previous_note_count,
            note_count,
            predecessor,
            successor,
            block_id,
        })
    }

    /// The exact bytes every quorum signer authenticates.
    pub fn signing_message(&self) -> [u8; FAITHFUL_NOTE_ROOT_RECORD_V1_BYTES] {
        let mut out = [0u8; FAITHFUL_NOTE_ROOT_RECORD_V1_BYTES];
        out[0..4].copy_from_slice(&RECORD_MAGIC);
        out[4..6].copy_from_slice(&VERSION_V1.to_le_bytes());
        out[6..8].copy_from_slice(&RESERVED_ZERO.to_le_bytes());
        out[8..40].copy_from_slice(&self.session_id);
        out[40..72].copy_from_slice(&self.federation_id);
        out[72..80].copy_from_slice(&self.committee_epoch.to_le_bytes());
        out[80..88].copy_from_slice(&self.previous_height.to_le_bytes());
        out[88..96].copy_from_slice(&self.height.to_le_bytes());
        out[96..104].copy_from_slice(&self.previous_note_count.to_le_bytes());
        out[104..112].copy_from_slice(&self.note_count.to_le_bytes());
        out[112..144].copy_from_slice(self.predecessor.as_bytes());
        out[144..176].copy_from_slice(self.successor.as_bytes());
        out[176..208].copy_from_slice(&self.block_id);
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> std::result::Result<Self, FaithfulNoteRootHistoryError> {
        if bytes.len() != FAITHFUL_NOTE_ROOT_RECORD_V1_BYTES {
            return Err(FaithfulNoteRootHistoryError::Malformed("record length"));
        }
        if bytes[0..4] != RECORD_MAGIC
            || u16::from_le_bytes(bytes[4..6].try_into().unwrap()) != VERSION_V1
            || u16::from_le_bytes(bytes[6..8].try_into().unwrap()) != RESERVED_ZERO
        {
            return Err(FaithfulNoteRootHistoryError::Malformed("record header"));
        }
        Self::new(
            bytes[8..40].try_into().unwrap(),
            bytes[40..72].try_into().unwrap(),
            u64::from_le_bytes(bytes[72..80].try_into().unwrap()),
            u64::from_le_bytes(bytes[80..88].try_into().unwrap()),
            u64::from_le_bytes(bytes[88..96].try_into().unwrap()),
            u64::from_le_bytes(bytes[96..104].try_into().unwrap()),
            u64::from_le_bytes(bytes[104..112].try_into().unwrap()),
            CanonicalFaithfulRoot::from_bytes(bytes[112..144].try_into().unwrap())?,
            CanonicalFaithfulRoot::from_bytes(bytes[144..176].try_into().unwrap())?,
            bytes[176..208].try_into().unwrap(),
        )
    }

    pub fn to_anchor(&self) -> FaithfulNoteRootAnchorV1 {
        FaithfulNoteRootAnchorV1 {
            session_id: self.session_id,
            federation_id: self.federation_id,
            committee_epoch: self.committee_epoch,
            height: self.height,
            note_count: self.note_count,
            root: self.successor,
        }
    }

    pub fn validate_extension(
        &self,
        anchor: &FaithfulNoteRootAnchorV1,
    ) -> std::result::Result<(), FaithfulNoteRootHistoryError> {
        if self.session_id != anchor.session_id {
            return Err(FaithfulNoteRootHistoryError::ContextMismatch("session"));
        }
        if self.federation_id != anchor.federation_id {
            return Err(FaithfulNoteRootHistoryError::ContextMismatch("federation"));
        }
        if self.committee_epoch != anchor.committee_epoch {
            return Err(FaithfulNoteRootHistoryError::ContextMismatch(
                "committee epoch",
            ));
        }
        if self.previous_height != anchor.height
            || self.height
                != anchor
                    .height
                    .checked_add(1)
                    .ok_or(FaithfulNoteRootHistoryError::NonConsecutiveHeight)?
        {
            return Err(FaithfulNoteRootHistoryError::NonConsecutiveHeight);
        }
        if self.previous_note_count != anchor.note_count {
            return Err(FaithfulNoteRootHistoryError::ContextMismatch(
                "predecessor note count",
            ));
        }
        if self.predecessor != anchor.root {
            return Err(FaithfulNoteRootHistoryError::ContextMismatch(
                "predecessor root",
            ));
        }
        Ok(())
    }
}

#[derive(Serialize, Deserialize)]
struct EnvelopeWireV1 {
    version: u16,
    record: Vec<u8>,
    hybrid_quorum: Vec<HybridQuorumSig>,
}

/// An exact transition plus its enrolled-roster hybrid quorum.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FaithfulNoteRootEnvelopeV1 {
    pub record: FaithfulNoteRootRecordV1,
    pub hybrid_quorum: Vec<HybridQuorumSig>,
}

impl FaithfulNoteRootEnvelopeV1 {
    pub fn verify_hybrid(
        &self,
        committee: &[PublicKey],
        ml_dsa_committee: &[MlDsaPublicKey],
        threshold: usize,
    ) -> bool {
        // `dregg-persist` is a light leaf: it cannot link the Lean archive from `[dependencies]`,
        // so nothing in its test binary installs a verified PQ core and `dregg-pq` refuses the
        // ML-DSA verify below with an uncatchable `process::abort()` — which is what this crate's
        // lib-test binary did. The dev-only `dregg-pq-testkit` links the archive and installs the
        // cores. `#[cfg(test)]` because the shipped crate stays archive-free; a node installs the
        // same cores at startup.
        #[cfg(test)]
        dregg_pq_testkit::install_or_panic();
        dregg_federation::receipt::verify_hybrid_quorum_sigs(
            &self.hybrid_quorum,
            &self.record.signing_message(),
            committee,
            ml_dsa_committee,
            threshold,
        )
    }

    pub(crate) fn to_bytes(&self) -> StoreResult<Vec<u8>> {
        if self.hybrid_quorum.len() > MAX_QUORUM_SIGNERS {
            return Err(integrity(FaithfulNoteRootHistoryError::Malformed(
                "quorum signer count",
            )));
        }
        let wire = EnvelopeWireV1 {
            version: VERSION_V1,
            record: self.record.signing_message().to_vec(),
            hybrid_quorum: self.hybrid_quorum.clone(),
        };
        let bytes = postcard::to_stdvec(&wire)?;
        if bytes.len() > MAX_ENVELOPE_BYTES {
            return Err(integrity(FaithfulNoteRootHistoryError::Malformed(
                "envelope size",
            )));
        }
        Ok(bytes)
    }

    pub(crate) fn from_bytes(bytes: &[u8]) -> StoreResult<Self> {
        if bytes.len() > MAX_ENVELOPE_BYTES {
            return Err(integrity(FaithfulNoteRootHistoryError::Malformed(
                "envelope size",
            )));
        }
        let (wire, remainder): (EnvelopeWireV1, &[u8]) = postcard::take_from_bytes(bytes)?;
        if !remainder.is_empty() || wire.version != VERSION_V1 {
            return Err(integrity(FaithfulNoteRootHistoryError::Malformed(
                "envelope framing",
            )));
        }
        if wire.hybrid_quorum.len() > MAX_QUORUM_SIGNERS {
            return Err(integrity(FaithfulNoteRootHistoryError::Malformed(
                "quorum signer count",
            )));
        }
        Ok(Self {
            record: FaithfulNoteRootRecordV1::from_bytes(&wire.record).map_err(integrity)?,
            hybrid_quorum: wire.hybrid_quorum,
        })
    }
}

/// External exact-head expectation.  A valid prefix is refused if it does not
/// match all four coordinates.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FaithfulNoteRootExpectationV1 {
    pub records: u64,
    pub height: u64,
    pub note_count: u64,
    pub root: CanonicalFaithfulRoot,
}

/// Store-minted evidence that one exact historical faithful root is covered by
/// the currently authenticated dense history index.
///
/// This is deliberately an opaque, non-`Clone`, non-serializable capability.
/// A caller can obtain it only from
/// [`PersistentStore::store_authenticated_historical_root_hybrid`], which
/// authenticates the requested row directly and authenticates the current
/// tail named by the atomically maintained head/index seal.  The finalizer
/// retains this value until its consuming store transaction, rather than
/// reducing the check to a caller-replayable `(height, root)` boolean.
///
/// This remains a trusted-store capability, not a portable proof.  The full
/// [`PersistentStore::load_faithful_note_root_history_hybrid`] replay remains
/// the boot/offline audit gate for the complete predecessor chain.
#[derive(Debug)]
pub struct StoreAuthenticatedHistoricalRoot {
    height: u64,
    root: CanonicalFaithfulRoot,
    _private: (),
}

impl StoreAuthenticatedHistoricalRoot {
    /// The exact authenticated height.  Exposed only for diagnostics; callers
    /// cannot construct or alter the capability.
    pub fn height(&self) -> u64 {
        self.height
    }

    /// The exact authenticated faithful-eight root.
    pub fn root(&self) -> CanonicalFaithfulRoot {
        self.root
    }
}

#[derive(Clone, Debug)]
pub struct FaithfulNoteRootHistoryV1 {
    anchor: FaithfulNoteRootAnchorV1,
    envelopes: Vec<FaithfulNoteRootEnvelopeV1>,
}

impl FaithfulNoteRootHistoryV1 {
    pub fn new(anchor: FaithfulNoteRootAnchorV1) -> Self {
        Self {
            anchor,
            envelopes: Vec::new(),
        }
    }

    pub fn anchor(&self) -> &FaithfulNoteRootAnchorV1 {
        &self.anchor
    }

    pub fn envelopes(&self) -> &[FaithfulNoteRootEnvelopeV1] {
        &self.envelopes
    }

    pub fn head(&self) -> FaithfulNoteRootAnchorV1 {
        self.envelopes
            .last()
            .map(|envelope| envelope.record.to_anchor())
            .unwrap_or_else(|| self.anchor.clone())
    }

    fn append_structurally(
        &mut self,
        envelope: FaithfulNoteRootEnvelopeV1,
    ) -> std::result::Result<(), FaithfulNoteRootHistoryError> {
        let head = self.head();
        if let Some(existing) = self
            .envelopes
            .iter()
            .find(|existing| existing.record.height == envelope.record.height)
        {
            return Err(if existing == &envelope {
                FaithfulNoteRootHistoryError::Replay
            } else {
                FaithfulNoteRootHistoryError::Fork
            });
        }
        if self
            .envelopes
            .iter()
            .any(|existing| existing.record.block_id == envelope.record.block_id)
        {
            return Err(FaithfulNoteRootHistoryError::DuplicateBlock);
        }
        envelope.record.validate_extension(&head)?;
        self.envelopes.push(envelope);
        Ok(())
    }

    pub fn append_hybrid(
        &mut self,
        envelope: FaithfulNoteRootEnvelopeV1,
        committee: &[PublicKey],
        ml_dsa_committee: &[MlDsaPublicKey],
        threshold: usize,
    ) -> std::result::Result<(), FaithfulNoteRootHistoryError> {
        if !envelope.verify_hybrid(committee, ml_dsa_committee, threshold) {
            return Err(FaithfulNoteRootHistoryError::AuthenticationFailed);
        }
        self.append_structurally(envelope)
    }

    pub fn verify_exact_snapshot(
        &self,
        expected: FaithfulNoteRootExpectationV1,
    ) -> std::result::Result<(), FaithfulNoteRootHistoryError> {
        let head = self.head();
        let actual_records = u64::try_from(self.envelopes.len()).map_err(|_| {
            FaithfulNoteRootHistoryError::Malformed("record count does not fit u64")
        })?;
        if actual_records != expected.records {
            return Err(FaithfulNoteRootHistoryError::SnapshotMismatch(
                "record count",
            ));
        }
        if head.height != expected.height {
            return Err(FaithfulNoteRootHistoryError::SnapshotMismatch("height"));
        }
        if head.note_count != expected.note_count {
            return Err(FaithfulNoteRootHistoryError::SnapshotMismatch("note count"));
        }
        if head.root != expected.root {
            return Err(FaithfulNoteRootHistoryError::SnapshotMismatch("head root"));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct HeadSealV1 {
    records: u64,
    head: FaithfulNoteRootAnchorV1,
}

impl HeadSealV1 {
    fn to_bytes(&self) -> [u8; FAITHFUL_NOTE_ROOT_HEAD_V1_BYTES] {
        let mut out = [0u8; FAITHFUL_NOTE_ROOT_HEAD_V1_BYTES];
        out[0..4].copy_from_slice(&HEAD_MAGIC);
        out[4..6].copy_from_slice(&VERSION_V1.to_le_bytes());
        out[6..8].copy_from_slice(&RESERVED_ZERO.to_le_bytes());
        out[8..16].copy_from_slice(&self.records.to_le_bytes());
        // The anchor's own header is redundant here; store only its payload.
        out[16..136].copy_from_slice(&self.head.to_bytes()[8..128]);
        out
    }

    fn from_bytes(bytes: &[u8]) -> std::result::Result<Self, FaithfulNoteRootHistoryError> {
        if bytes.len() != FAITHFUL_NOTE_ROOT_HEAD_V1_BYTES
            || bytes[0..4] != HEAD_MAGIC
            || u16::from_le_bytes(bytes[4..6].try_into().unwrap()) != VERSION_V1
            || u16::from_le_bytes(bytes[6..8].try_into().unwrap()) != RESERVED_ZERO
        {
            return Err(FaithfulNoteRootHistoryError::Malformed("head seal"));
        }
        let records = u64::from_le_bytes(bytes[8..16].try_into().unwrap());
        let mut anchor = [0u8; FAITHFUL_NOTE_ROOT_ANCHOR_V1_BYTES];
        anchor[0..4].copy_from_slice(&ANCHOR_MAGIC);
        anchor[4..6].copy_from_slice(&VERSION_V1.to_le_bytes());
        anchor[6..8].copy_from_slice(&RESERVED_ZERO.to_le_bytes());
        anchor[8..128].copy_from_slice(&bytes[16..136]);
        Ok(Self {
            records,
            head: FaithfulNoteRootAnchorV1::from_bytes(&anchor)?,
        })
    }
}

impl PersistentStore {
    /// Read the structurally sealed faithful history head.
    ///
    /// `None` means this store has not started a v1 segment.  A half-installed
    /// anchor/head or a record-count disagreement is an integrity error, never
    /// treated as an empty legacy store.  Authentication of the rows is checked
    /// by [`Self::load_faithful_note_root_history_hybrid`]; this narrow read is
    /// used only to plan the next locally-authenticated atomic append.
    pub fn faithful_note_root_head(&self) -> StoreResult<Option<FaithfulNoteRootAnchorV1>> {
        let read = self.db.begin_read()?;
        let table = read.open_table(tables::FAITHFUL_NOTE_ROOT_HISTORY)?;
        let metadata = read.open_table(tables::METADATA_BYTES)?;
        let anchor = metadata
            .get(tables::META_FAITHFUL_NOTE_ROOT_ANCHOR)?
            .map(|guard| guard.value().to_vec());
        let seal = metadata
            .get(tables::META_FAITHFUL_NOTE_ROOT_HEAD)?
            .map(|guard| guard.value().to_vec());
        match (anchor, seal) {
            (None, None) if table.is_empty()? => Ok(None),
            (Some(anchor), Some(seal)) => {
                let _ = FaithfulNoteRootAnchorV1::from_bytes(&anchor).map_err(integrity)?;
                let seal = HeadSealV1::from_bytes(&seal).map_err(integrity)?;
                if table.len()? != seal.records {
                    return Err(integrity(FaithfulNoteRootHistoryError::SnapshotMismatch(
                        "persisted record count",
                    )));
                }
                Ok(Some(seal.head))
            }
            _ => Err(integrity(FaithfulNoteRootHistoryError::Malformed(
                "partial anchor/head",
            ))),
        }
    }

    /// Exact externally-checkable seal coordinates for restart admission.
    pub fn faithful_note_root_expectation(
        &self,
    ) -> StoreResult<Option<FaithfulNoteRootExpectationV1>> {
        let read = self.db.begin_read()?;
        let table = read.open_table(tables::FAITHFUL_NOTE_ROOT_HISTORY)?;
        let metadata = read.open_table(tables::METADATA_BYTES)?;
        let anchor_present = metadata
            .get(tables::META_FAITHFUL_NOTE_ROOT_ANCHOR)?
            .is_some();
        let seal = metadata
            .get(tables::META_FAITHFUL_NOTE_ROOT_HEAD)?
            .map(|guard| guard.value().to_vec());
        match (anchor_present, seal) {
            (false, None) if table.is_empty()? => Ok(None),
            (true, Some(seal)) => {
                let seal = HeadSealV1::from_bytes(&seal).map_err(integrity)?;
                if table.len()? != seal.records {
                    return Err(integrity(FaithfulNoteRootHistoryError::SnapshotMismatch(
                        "persisted record count",
                    )));
                }
                Ok(Some(FaithfulNoteRootExpectationV1 {
                    records: seal.records,
                    height: seal.head.height,
                    note_count: seal.head.note_count,
                    root: seal.head.root,
                }))
            }
            _ => Err(integrity(FaithfulNoteRootHistoryError::Malformed(
                "partial anchor/head",
            ))),
        }
    }

    /// Mint O(1) store authority for one authenticated historical root.
    ///
    /// The direct row is hybrid-authenticated under the supplied enrolled
    /// roster.  Independently, the current tail row is hybrid-authenticated and
    /// required to equal the atomically maintained head seal.  Exact table
    /// cardinality plus the anchor/head height span and first/last keys prove
    /// that the redb index is dense, so a deleted/rekeyed row or stale head seal
    /// cannot be read as membership.  The anchor itself is the externally
    /// installed start authority and is admitted through the same sealed
    /// boundary.
    ///
    /// Unlike full replay, this does not reconstruct every predecessor edge.
    /// Full replay remains mandatory at boot/pre-activation and for offline
    /// audit; the online finalizer needs only authenticated membership of the
    /// exact `(height, root)` it consumes.
    pub fn store_authenticated_historical_root_hybrid(
        &self,
        committee: &[PublicKey],
        ml_dsa_committee: &[MlDsaPublicKey],
        threshold: usize,
        height: u64,
        root: [u8; 32],
    ) -> StoreResult<Option<StoreAuthenticatedHistoricalRoot>> {
        self.store_authenticated_historical_root_with(height, root, |envelope| {
            envelope.verify_hybrid(committee, ml_dsa_committee, threshold)
        })
    }

    fn store_authenticated_historical_root_with(
        &self,
        height: u64,
        root: [u8; 32],
        authenticate: impl Fn(&FaithfulNoteRootEnvelopeV1) -> bool,
    ) -> StoreResult<Option<StoreAuthenticatedHistoricalRoot>> {
        let Ok(root) = CanonicalFaithfulRoot::from_bytes(root) else {
            return Ok(None);
        };
        let read = self.db.begin_read()?;
        let table = read.open_table(tables::FAITHFUL_NOTE_ROOT_HISTORY)?;
        let metadata = read.open_table(tables::METADATA_BYTES)?;
        let anchor_guard = metadata
            .get(tables::META_FAITHFUL_NOTE_ROOT_ANCHOR)?
            .ok_or_else(|| integrity(FaithfulNoteRootHistoryError::Malformed("missing anchor")))?;
        let anchor =
            FaithfulNoteRootAnchorV1::from_bytes(anchor_guard.value()).map_err(integrity)?;
        let head_guard = metadata
            .get(tables::META_FAITHFUL_NOTE_ROOT_HEAD)?
            .ok_or_else(|| {
                integrity(FaithfulNoteRootHistoryError::Malformed("missing head seal"))
            })?;
        let seal = HeadSealV1::from_bytes(head_guard.value()).map_err(integrity)?;
        if table.len()? != seal.records {
            return Err(integrity(FaithfulNoteRootHistoryError::SnapshotMismatch(
                "persisted record count",
            )));
        }
        if seal.head.session_id != anchor.session_id
            || seal.head.federation_id != anchor.federation_id
            || seal.head.committee_epoch != anchor.committee_epoch
        {
            return Err(integrity(FaithfulNoteRootHistoryError::SnapshotMismatch(
                "head context",
            )));
        }
        let height_span = seal.head.height.checked_sub(anchor.height).ok_or_else(|| {
            integrity(FaithfulNoteRootHistoryError::SnapshotMismatch(
                "head height",
            ))
        })?;
        if height_span != seal.records {
            return Err(integrity(FaithfulNoteRootHistoryError::SnapshotMismatch(
                "dense height span",
            )));
        }

        if seal.records == 0 {
            if !table.is_empty()? || seal.head != anchor {
                return Err(integrity(FaithfulNoteRootHistoryError::SnapshotMismatch(
                    "empty sealed boundary",
                )));
            }
        } else {
            let expected_first = anchor
                .height
                .checked_add(1)
                .ok_or_else(|| integrity(FaithfulNoteRootHistoryError::NonConsecutiveHeight))?;
            let (first_key, _) = table.first()?.ok_or_else(|| {
                integrity(FaithfulNoteRootHistoryError::SnapshotMismatch(
                    "missing first row",
                ))
            })?;
            let (last_key, last_bytes) = table.last()?.ok_or_else(|| {
                integrity(FaithfulNoteRootHistoryError::SnapshotMismatch(
                    "missing tail row",
                ))
            })?;
            if first_key.value() != expected_first || last_key.value() != seal.head.height {
                return Err(integrity(FaithfulNoteRootHistoryError::SnapshotMismatch(
                    "dense height boundary",
                )));
            }
            let tail = FaithfulNoteRootEnvelopeV1::from_bytes(last_bytes.value())?;
            if tail.to_bytes()?.as_slice() != last_bytes.value()
                || tail.record.height != last_key.value()
                || tail.record.to_anchor() != seal.head
                || !authenticate(&tail)
            {
                return Err(integrity(FaithfulNoteRootHistoryError::SnapshotMismatch(
                    "authenticated head seal",
                )));
            }
        }

        let authenticated = if height == anchor.height {
            root == anchor.root
        } else if height > anchor.height && height <= seal.head.height {
            let Some(row_bytes) = table.get(height)? else {
                return Err(integrity(FaithfulNoteRootHistoryError::SnapshotMismatch(
                    "missing dense row",
                )));
            };
            let envelope = FaithfulNoteRootEnvelopeV1::from_bytes(row_bytes.value())?;
            envelope.to_bytes()?.as_slice() == row_bytes.value()
                && envelope.record.height == height
                && envelope.record.session_id == anchor.session_id
                && envelope.record.federation_id == anchor.federation_id
                && envelope.record.committee_epoch == anchor.committee_epoch
                && envelope.record.successor == root
                && authenticate(&envelope)
        } else {
            false
        };
        Ok(authenticated.then_some(StoreAuthenticatedHistoricalRoot {
            height,
            root,
            _private: (),
        }))
    }

    /// Install the external genesis/current anchor for the dedicated v1 table.
    /// Re-opening with the exact same anchor is idempotent; a different anchor
    /// refuses, so a caller cannot silently re-session existing history.
    pub fn initialize_faithful_note_root_history(
        &self,
        anchor: &FaithfulNoteRootAnchorV1,
    ) -> StoreResult<()> {
        let anchor_bytes = anchor.to_bytes();
        let head_bytes = HeadSealV1 {
            records: 0,
            head: anchor.clone(),
        }
        .to_bytes();
        let write = self.db.begin_write()?;
        {
            let table = write.open_table(tables::FAITHFUL_NOTE_ROOT_HISTORY)?;
            let mut metadata = write.open_table(tables::METADATA_BYTES)?;
            let existing_anchor = metadata
                .get(tables::META_FAITHFUL_NOTE_ROOT_ANCHOR)?
                .map(|guard| guard.value().to_vec());
            match existing_anchor {
                Some(existing) if existing.as_slice() != anchor_bytes.as_slice() => {
                    return Err(integrity(FaithfulNoteRootHistoryError::ContextMismatch(
                        "installed anchor",
                    )));
                }
                Some(_) => {}
                None => {
                    if !table.is_empty()? {
                        return Err(integrity(FaithfulNoteRootHistoryError::Malformed(
                            "records without anchor",
                        )));
                    }
                    metadata.insert(
                        tables::META_FAITHFUL_NOTE_ROOT_ANCHOR,
                        anchor_bytes.as_slice(),
                    )?;
                    metadata.insert(tables::META_FAITHFUL_NOTE_ROOT_HEAD, head_bytes.as_slice())?;
                }
            }
        }
        write.commit()?;
        Ok(())
    }

    /// Append only after the exact record passes the enrolled-roster hybrid
    /// quorum with distinct enrolled ML-DSA keys. Structural validation and
    /// the table/head-seal mutation happen under one redb writer transaction.
    pub fn append_faithful_note_root_hybrid(
        &self,
        envelope: &FaithfulNoteRootEnvelopeV1,
        committee: &[PublicKey],
        ml_dsa_committee: &[MlDsaPublicKey],
        threshold: usize,
    ) -> StoreResult<()> {
        if ml_dsa_committee
            .iter()
            .enumerate()
            .any(|(i, key)| ml_dsa_committee[..i].contains(key))
            || !envelope.verify_hybrid(committee, ml_dsa_committee, threshold)
        {
            return Err(integrity(
                FaithfulNoteRootHistoryError::AuthenticationFailed,
            ));
        }
        self.append_faithful_note_root_verified(envelope)
    }

    fn append_faithful_note_root_verified(
        &self,
        envelope: &FaithfulNoteRootEnvelopeV1,
    ) -> StoreResult<()> {
        let write = self.db.begin_write()?;
        append_faithful_note_root_verified_in(&write, envelope, None, false)?;
        write.commit()?;
        Ok(())
    }

    /// Load, replay, and authenticate every record, then compare the exact
    /// externally expected head.  A truncated row, trailing bytes, a deleted
    /// tail with a surviving head seal, a fork, replay, or bad hybrid signature
    /// refuses.  Rollback of the database *and* the caller's expected head is,
    /// necessarily, an external checkpoint/finality problem.
    pub fn load_faithful_note_root_history_hybrid(
        &self,
        committee: &[PublicKey],
        ml_dsa_committee: &[MlDsaPublicKey],
        threshold: usize,
        expected: FaithfulNoteRootExpectationV1,
    ) -> StoreResult<FaithfulNoteRootHistoryV1> {
        self.load_faithful_note_root_history_with(expected, |envelope| {
            envelope.verify_hybrid(committee, ml_dsa_committee, threshold)
        })
    }

    /// [`Self::load_faithful_note_root_history_hybrid`], also returning the
    /// store-minted [`AuthenticatedFaithfulNoteRootPrefix`] for the rows it
    /// authenticated, which the roster may sign into a new audit seal.
    ///
    /// A version-2 seal binds the threshold and ordered classical/PQ enrollment
    /// policy captured when its private prefix was minted. Its complete signed
    /// statement must match the current policy, anchor, row count, and exact
    /// stored-byte digest, and its quorum must verify under that same policy.
    /// Legacy, mismatched, malformed, or unverifiable seals fall back to rows.
    /// The seal attests to a completed same-policy audit; it is not a proof
    /// against a quorum deliberately signing a false audit assertion.
    pub fn load_faithful_note_root_history_hybrid_audited(
        &self,
        committee: &[PublicKey],
        ml_dsa_committee: &[MlDsaPublicKey],
        threshold: usize,
        expected: FaithfulNoteRootExpectationV1,
    ) -> StoreResult<(FaithfulNoteRootHistoryV1, AuthenticatedFaithfulNoteRootPrefix)> {
        self.load_faithful_note_root_history_audited_with(
            expected,
            faithful_note_root_audit_policy(committee, ml_dsa_committee, threshold),
            |envelope| envelope.verify_hybrid(committee, ml_dsa_committee, threshold),
            |statement, quorum| {
                dregg_federation::receipt::verify_hybrid_quorum_sigs(
                    quorum,
                    statement,
                    committee,
                    ml_dsa_committee,
                    threshold,
                )
            },
        )
    }

    /// Persist a quorum over `prefix`'s statement as the history's audit seal,
    /// replacing any earlier one.  The quorum is not checked here: a load
    /// verifies it before relying on it, and ignores it otherwise.
    pub fn store_faithful_note_root_audit_seal(
        &self,
        prefix: &AuthenticatedFaithfulNoteRootPrefix,
        hybrid_quorum: Vec<HybridQuorumSig>,
    ) -> StoreResult<()> {
        if prefix.policy.is_none() {
            return Err(integrity(FaithfulNoteRootHistoryError::AuthenticationFailed));
        }
        let seal = FaithfulNoteRootAuditSealV1 {
            statement: prefix.statement,
            hybrid_quorum,
        };
        let bytes = seal.to_bytes()?;
        let write = self.db.begin_write()?;
        {
            let mut metadata = write.open_table(tables::METADATA_BYTES)?;
            metadata.insert(tables::META_FAITHFUL_NOTE_ROOT_AUDIT, bytes.as_slice())?;
        }
        write.commit()?;
        Ok(())
    }

    fn load_faithful_note_root_history_with(
        &self,
        expected: FaithfulNoteRootExpectationV1,
        authenticate: impl Fn(&FaithfulNoteRootEnvelopeV1) -> bool + Sync,
    ) -> StoreResult<FaithfulNoteRootHistoryV1> {
        self.load_faithful_note_root_history_audited_with(expected, None, authenticate, |_, _| false)
            .map(|(history, _)| history)
    }

    /// Consume decoded rows and structural/authentication verdicts in key order.
    /// Only an exact policy-bound seal substitutes for covered row checks.
    /// Uncovered rows authenticate in parallel but their verdicts are consumed
    /// serially; ignored seals leave every row on that existing refusal path.
    fn load_faithful_note_root_history_audited_with(
        &self,
        expected: FaithfulNoteRootExpectationV1,
        policy: Option<[u8; 32]>,
        authenticate: impl Fn(&FaithfulNoteRootEnvelopeV1) -> bool + Sync,
        authenticate_seal: impl Fn(&[u8], &[HybridQuorumSig]) -> bool,
    ) -> StoreResult<(FaithfulNoteRootHistoryV1, AuthenticatedFaithfulNoteRootPrefix)> {
        let read = self.db.begin_read()?;
        let table = read.open_table(tables::FAITHFUL_NOTE_ROOT_HISTORY)?;
        let metadata = read.open_table(tables::METADATA_BYTES)?;
        let anchor_guard = metadata
            .get(tables::META_FAITHFUL_NOTE_ROOT_ANCHOR)?
            .ok_or_else(|| integrity(FaithfulNoteRootHistoryError::Malformed("missing anchor")))?;
        let anchor =
            FaithfulNoteRootAnchorV1::from_bytes(anchor_guard.value()).map_err(integrity)?;
        let head_guard = metadata
            .get(tables::META_FAITHFUL_NOTE_ROOT_HEAD)?
            .ok_or_else(|| {
                integrity(FaithfulNoteRootHistoryError::Malformed("missing head seal"))
            })?;
        let seal = HeadSealV1::from_bytes(head_guard.value()).map_err(integrity)?;
        if table.len()? != seal.records {
            return Err(integrity(FaithfulNoteRootHistoryError::SnapshotMismatch(
                "persisted record count",
            )));
        }

        let audit_seal = metadata
            .get(tables::META_FAITHFUL_NOTE_ROOT_AUDIT)?
            .and_then(|guard| FaithfulNoteRootAuditSealV1::from_bytes(guard.value()))
            .filter(|seal| seal.records() > 0);

        // Decode rows up to the first undecodable one; its error is raised only
        // after every earlier row has had its own checks, as in a serial loop.
        let mut rows = Vec::new();
        let mut decode_error = None;
        let mut digest = audit_prefix_hasher();
        let mut sealed_digest = None;
        for entry in table.iter()? {
            let decoded = entry.map_err(StoreError::from).and_then(|(height, bytes)| {
                let envelope = FaithfulNoteRootEnvelopeV1::from_bytes(bytes.value())?;
                if envelope.record.height != height.value() {
                    return Err(integrity(FaithfulNoteRootHistoryError::Malformed(
                        "height key",
                    )));
                }
                absorb_audit_row(&mut digest, height.value(), bytes.value());
                Ok(envelope)
            });
            match decoded {
                Ok(envelope) => rows.push(envelope),
                Err(e) => {
                    decode_error = Some(e);
                    break;
                }
            }
            if audit_seal
                .as_ref()
                .is_some_and(|seal| seal.records() == rows.len() as u64)
            {
                sealed_digest = Some(*digest.finalize().as_bytes());
            }
        }

        let sealed = match (&audit_seal, sealed_digest, policy) {
            (Some(seal), Some(prefix_digest), Some(policy))
                if seal.statement
                    == audit_statement(&anchor, seal.records(), &prefix_digest, &policy)
                    && authenticate_seal(&seal.statement, &seal.hybrid_quorum) =>
            {
                rows.len().min(seal.records() as usize)
            }
            _ => 0,
        };
        let records = rows.len() as u64;
        let mut authentic = vec![true; sealed];
        authentic.extend(authenticate_rows(&rows[sealed..], &authenticate));
        let mut history = FaithfulNoteRootHistoryV1::new(anchor.clone());
        for (envelope, authentic) in rows.into_iter().zip(authentic) {
            if !authentic {
                return Err(integrity(
                    FaithfulNoteRootHistoryError::AuthenticationFailed,
                ));
            }
            history.append_structurally(envelope).map_err(integrity)?;
        }
        if let Some(e) = decode_error {
            return Err(e);
        }
        if history.head() != seal.head {
            return Err(integrity(FaithfulNoteRootHistoryError::SnapshotMismatch(
                "persisted head seal",
            )));
        }
        history.verify_exact_snapshot(expected).map_err(integrity)?;
        let prefix = AuthenticatedFaithfulNoteRootPrefix {
            statement: audit_statement(
                &anchor,
                records,
                digest.finalize().as_bytes(),
                &policy.unwrap_or([0; 32]),
            ),
            policy,
            sealed_records: sealed as u64,
        };
        Ok((history, prefix))
    }
}

const AUDIT_MAGIC: [u8; 4] = *b"FNHS";
const AUDIT_VERSION_V2: u16 = 2;
/// `magic(4) || version(2) || reserved(2) || anchor(128) || records(8) || digest(32) || policy(32)`.
pub const FAITHFUL_NOTE_ROOT_AUDIT_V2_BYTES: usize = 208;

/// The fixed-width statement an audit seal's quorum signs: the first `records`
/// rows of the segment starting at `anchor`, whose exact stored bytes hash to
/// `digest`, were each authenticated under `policy`. Its magic keeps it
/// apart from a row's `FNHR` signing message.
fn audit_statement(
    anchor: &FaithfulNoteRootAnchorV1,
    records: u64,
    digest: &[u8; 32],
    policy: &[u8; 32],
) -> [u8; FAITHFUL_NOTE_ROOT_AUDIT_V2_BYTES] {
    let mut out = [0u8; FAITHFUL_NOTE_ROOT_AUDIT_V2_BYTES];
    out[0..4].copy_from_slice(&AUDIT_MAGIC);
    out[4..6].copy_from_slice(&AUDIT_VERSION_V2.to_le_bytes());
    out[6..8].copy_from_slice(&RESERVED_ZERO.to_le_bytes());
    out[8..136].copy_from_slice(&anchor.to_bytes());
    out[136..144].copy_from_slice(&records.to_le_bytes());
    out[144..176].copy_from_slice(digest);
    out[176..208].copy_from_slice(policy);
    out
}

fn audit_prefix_hasher() -> blake3::Hasher {
    blake3::Hasher::new_derive_key("dregg faithful note-root history audit prefix v1")
}

/// Exact cache policy: threshold followed by ordered classical/PQ pairs.
/// Duplicate classical identities are not cache-eligible; no set normalization.
/// Ineligible policies fall back to row authentication, not an early error.
fn faithful_note_root_audit_policy(
    committee: &[PublicKey],
    ml_dsa_committee: &[MlDsaPublicKey],
    threshold: usize,
) -> Option<[u8; 32]> {
    if threshold == 0
        || threshold > committee.len()
        || committee.len() != ml_dsa_committee.len()
    {
        return None;
    }
    let threshold = u64::try_from(threshold).ok()?;
    let members = u64::try_from(committee.len()).ok()?;
    let mut seen = std::collections::HashSet::new();
    let mut policy =
        blake3::Hasher::new_derive_key("dregg faithful note-root history audit policy v2");
    policy.update(&threshold.to_le_bytes());
    policy.update(&members.to_le_bytes());
    for (classical, pq) in committee.iter().zip(ml_dsa_committee) {
        if !seen.insert(classical.0) {
            return None;
        }
        policy.update(&classical.0);
        policy.update(&(pq.0.len() as u64).to_le_bytes());
        policy.update(&pq.0);
    }
    Some(*policy.finalize().as_bytes())
}

/// Bind each row's key and exact stored bytes, length-prefixed, in key order.
fn absorb_audit_row(hasher: &mut blake3::Hasher, height: u64, bytes: &[u8]) {
    hasher.update(&height.to_le_bytes());
    hasher.update(&(bytes.len() as u64).to_le_bytes());
    hasher.update(bytes);
}

/// A roster quorum over the policy-bound version-2 [`audit_statement`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FaithfulNoteRootAuditSealV1 {
    statement: [u8; FAITHFUL_NOTE_ROOT_AUDIT_V2_BYTES],
    hybrid_quorum: Vec<HybridQuorumSig>,
}

#[derive(Serialize, Deserialize)]
struct AuditSealWireV1 {
    version: u16,
    statement: Vec<u8>,
    hybrid_quorum: Vec<HybridQuorumSig>,
}

impl FaithfulNoteRootAuditSealV1 {
    fn records(&self) -> u64 {
        u64::from_le_bytes(self.statement[136..144].try_into().unwrap())
    }

    fn to_bytes(&self) -> StoreResult<Vec<u8>> {
        if self.hybrid_quorum.len() > MAX_QUORUM_SIGNERS {
            return Err(integrity(FaithfulNoteRootHistoryError::Malformed(
                "quorum signer count",
            )));
        }
        Ok(postcard::to_stdvec(&AuditSealWireV1 {
            version: AUDIT_VERSION_V2,
            statement: self.statement.to_vec(),
            hybrid_quorum: self.hybrid_quorum.clone(),
        })?)
    }

    /// Only a version-2 policy-bound seal is cache evidence. Legacy version-1
    /// seals and malformed values return `None`, so a load checks every row.
    fn from_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() > MAX_ENVELOPE_BYTES {
            return None;
        }
        let (wire, remainder): (AuditSealWireV1, &[u8]) = postcard::take_from_bytes(bytes).ok()?;
        if !remainder.is_empty()
            || wire.version != AUDIT_VERSION_V2
            || wire.hybrid_quorum.len() > MAX_QUORUM_SIGNERS
        {
            return None;
        }
        Some(Self {
            statement: wire.statement.try_into().ok()?,
            hybrid_quorum: wire.hybrid_quorum,
        })
    }
}

/// Store-minted evidence from a completed replay, bound to that replay's exact
/// cache-eligible policy. Private fields prevent a caller changing mint policy.
/// A replay without an eligible policy may return evidence, but it cannot be
/// persisted as an audit seal.
#[derive(Debug)]
pub struct AuthenticatedFaithfulNoteRootPrefix {
    statement: [u8; FAITHFUL_NOTE_ROOT_AUDIT_V2_BYTES],
    policy: Option<[u8; 32]>,
    sealed_records: u64,
}

impl AuthenticatedFaithfulNoteRootPrefix {
    /// The exact bytes a roster quorum signs to seal these rows.
    pub fn statement(&self) -> &[u8] {
        &self.statement
    }

    /// Rows authenticated by this load.
    pub fn records(&self) -> u64 {
        u64::from_le_bytes(self.statement[136..144].try_into().unwrap())
    }

    /// How many of them a verified audit seal covered (no per-row check).
    pub fn sealed_records(&self) -> u64 {
        self.sealed_records
    }
}

/// Authenticate every row on all available cores and return one verdict per row.
///
/// Every row before the first failing one is checked; a row after a known failure
/// is reported `false` without being checked, because the serial decision loop
/// stops at the earlier failure and never reads it.
fn authenticate_rows(
    rows: &[FaithfulNoteRootEnvelopeV1],
    authenticate: &(impl Fn(&FaithfulNoteRootEnvelopeV1) -> bool + Sync),
) -> Vec<bool> {
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

    let workers = std::thread::available_parallelism()
        .map_or(1, std::num::NonZeroUsize::get)
        .min(rows.len());
    if workers <= 1 {
        let mut verdicts = vec![false; rows.len()];
        for (verdict, row) in verdicts.iter_mut().zip(rows) {
            *verdict = authenticate(row);
            if !*verdict {
                break;
            }
        }
        return verdicts;
    }
    let verdicts: Vec<AtomicBool> = rows.iter().map(|_| AtomicBool::new(false)).collect();
    let next = AtomicUsize::new(0);
    let first_failure = AtomicUsize::new(usize::MAX);
    std::thread::scope(|scope| {
        for _ in 0..workers {
            scope.spawn(|| {
                loop {
                    let i = next.fetch_add(1, Ordering::Relaxed);
                    if i >= rows.len() || i > first_failure.load(Ordering::Relaxed) {
                        break;
                    }
                    if authenticate(&rows[i]) {
                        verdicts[i].store(true, Ordering::Relaxed);
                    } else {
                        first_failure.fetch_min(i, Ordering::Relaxed);
                    }
                }
            });
        }
    });
    verdicts.into_iter().map(AtomicBool::into_inner).collect()
}

/// Append or replay-check one faithful transition inside a caller-owned redb
/// transaction.  This is crate-private because only the finalized commit weld
/// may couple history mutation to note leaves and the commit cursor.
///
/// When the store has no segment yet, `initial_anchor` must be the exact
/// predecessor reconstructed from the durable note table.  `allow_replay` is
/// used only by the already-committed idempotence path: it reconstructs the complete current
/// chain/head and requires byte-identical membership at the requested historical height.  It
/// never patches a missing row, requires the old edge to remain the tail, or rewinds the seal.
pub(crate) fn append_faithful_note_root_verified_in(
    write: &redb::WriteTransaction,
    envelope: &FaithfulNoteRootEnvelopeV1,
    initial_anchor: Option<&FaithfulNoteRootAnchorV1>,
    allow_replay: bool,
) -> StoreResult<()> {
    let envelope_bytes = envelope.to_bytes()?;
    let mut table = write.open_table(tables::FAITHFUL_NOTE_ROOT_HISTORY)?;
    let mut metadata = write.open_table(tables::METADATA_BYTES)?;

    let anchor_bytes = metadata
        .get(tables::META_FAITHFUL_NOTE_ROOT_ANCHOR)?
        .map(|guard| guard.value().to_vec());
    let seal_bytes = metadata
        .get(tables::META_FAITHFUL_NOTE_ROOT_HEAD)?
        .map(|guard| guard.value().to_vec());

    let (installed_anchor, seal) = match (anchor_bytes, seal_bytes) {
        (Some(anchor_bytes), Some(seal_bytes)) => {
            let installed =
                FaithfulNoteRootAnchorV1::from_bytes(&anchor_bytes).map_err(integrity)?;
            if let Some(expected) = initial_anchor
                && installed != *expected
            {
                return Err(integrity(FaithfulNoteRootHistoryError::ContextMismatch(
                    "installed anchor",
                )));
            }
            let seal = HeadSealV1::from_bytes(&seal_bytes).map_err(integrity)?;
            (installed, seal)
        }
        (None, None) => {
            if !table.is_empty()? {
                return Err(integrity(FaithfulNoteRootHistoryError::Malformed(
                    "records without anchor",
                )));
            }
            // Replay is read-only.  In particular, a missing historical segment may not install
            // an anchor/head as a side effect before reporting that the requested row is absent.
            if allow_replay {
                return Err(integrity(FaithfulNoteRootHistoryError::SnapshotMismatch(
                    "missing replay record",
                )));
            }
            let initial = initial_anchor.ok_or_else(|| {
                integrity(FaithfulNoteRootHistoryError::Malformed(
                    "missing initial anchor",
                ))
            })?;
            let anchor_bytes = initial.to_bytes();
            let seal = HeadSealV1 {
                records: 0,
                head: initial.clone(),
            };
            let seal_bytes = seal.to_bytes();
            metadata.insert(
                tables::META_FAITHFUL_NOTE_ROOT_ANCHOR,
                anchor_bytes.as_slice(),
            )?;
            metadata.insert(tables::META_FAITHFUL_NOTE_ROOT_HEAD, seal_bytes.as_slice())?;
            (initial.clone(), seal)
        }
        _ => {
            return Err(integrity(FaithfulNoteRootHistoryError::Malformed(
                "partial anchor/head",
            )));
        }
    };

    if table.len()? != seal.records {
        return Err(integrity(FaithfulNoteRootHistoryError::SnapshotMismatch(
            "persisted record count",
        )));
    }

    if allow_replay {
        // An idempotent replay may name any immutable historical edge, not only the current tail.
        // Rebuild the complete installed chain before accepting membership: a byte-identical old
        // row beside a truncated, forked, non-canonical, or head-disagreeing current history is
        // still corrupt and must fail.  This path performs no writes and never rewinds the seal.
        let mut history = FaithfulNoteRootHistoryV1::new(installed_anchor);
        let mut found = false;
        for entry in table.iter()? {
            let (height, bytes) = entry?;
            let stored_bytes = bytes.value();
            let decoded = FaithfulNoteRootEnvelopeV1::from_bytes(stored_bytes)?;
            if decoded.to_bytes()?.as_slice() != stored_bytes {
                return Err(integrity(FaithfulNoteRootHistoryError::Malformed(
                    "non-canonical replay envelope",
                )));
            }
            if decoded.record.height != height.value() {
                return Err(integrity(FaithfulNoteRootHistoryError::Malformed(
                    "height key",
                )));
            }
            if decoded.record.height == envelope.record.height {
                if decoded != *envelope {
                    return Err(integrity(FaithfulNoteRootHistoryError::Fork));
                }
                found = true;
            }
            history.append_structurally(decoded).map_err(integrity)?;
        }
        if history.head() != seal.head {
            return Err(integrity(FaithfulNoteRootHistoryError::SnapshotMismatch(
                "persisted head seal",
            )));
        }
        if !found {
            return Err(integrity(FaithfulNoteRootHistoryError::SnapshotMismatch(
                "missing replay record",
            )));
        }
        return Ok(());
    }

    if let Some(existing) = table.get(envelope.record.height)? {
        let decoded = FaithfulNoteRootEnvelopeV1::from_bytes(existing.value())?;
        return Err(integrity(if decoded == *envelope {
            FaithfulNoteRootHistoryError::Replay
        } else {
            FaithfulNoteRootHistoryError::Fork
        }));
    }

    // A reused block id is replay even if an attacker changes height.
    for entry in table.iter()? {
        let (_, value) = entry?;
        let decoded = FaithfulNoteRootEnvelopeV1::from_bytes(value.value())?;
        if decoded.record.block_id == envelope.record.block_id {
            return Err(integrity(FaithfulNoteRootHistoryError::DuplicateBlock));
        }
    }

    envelope
        .record
        .validate_extension(&seal.head)
        .map_err(integrity)?;
    table.insert(envelope.record.height, envelope_bytes.as_slice())?;
    let next_seal = HeadSealV1 {
        records: seal.records.checked_add(1).ok_or_else(|| {
            integrity(FaithfulNoteRootHistoryError::Malformed(
                "record count overflow",
            ))
        })?,
        head: envelope.record.to_anchor(),
    }
    .to_bytes();
    metadata.insert(tables::META_FAITHFUL_NOTE_ROOT_HEAD, next_seal.as_slice())?;
    Ok(())
}

/// Build the exact next transition from the production faithful tree without
/// mutating the live tree.  This is the root-producer adapter the finalized
/// turn path can call once its authentication and atomic append weld land.
pub fn plan_faithful_note_root_transition_v1(
    tree: &crate::Poseidon2NoteTree,
    anchor: &FaithfulNoteRootAnchorV1,
    block_id: [u8; 32],
    new_commitments: &[[u8; 32]],
) -> std::result::Result<FaithfulNoteRootRecordV1, FaithfulNoteRootHistoryError> {
    let live_count = u64::try_from(tree.size())
        .map_err(|_| FaithfulNoteRootHistoryError::Malformed("live note count does not fit u64"))?;
    if live_count != anchor.note_count {
        return Err(FaithfulNoteRootHistoryError::ContextMismatch(
            "live note count",
        ));
    }
    let live_root = CanonicalFaithfulRoot::from_faithful(tree.faithful_root_immutable());
    if live_root != anchor.root {
        return Err(FaithfulNoteRootHistoryError::ContextMismatch(
            "live predecessor root",
        ));
    }
    let mut successor_tree = tree.clone();
    for commitment in new_commitments {
        successor_tree.append_blake3_commitment(commitment);
    }
    let added_count = u64::try_from(new_commitments.len())
        .map_err(|_| FaithfulNoteRootHistoryError::Malformed("append count does not fit u64"))?;
    let next_count = anchor.note_count.checked_add(added_count).ok_or(
        FaithfulNoteRootHistoryError::Malformed("note count overflow"),
    )?;
    FaithfulNoteRootRecordV1::new(
        anchor.session_id,
        anchor.federation_id,
        anchor.committee_epoch,
        anchor.height,
        anchor
            .height
            .checked_add(1)
            .ok_or(FaithfulNoteRootHistoryError::NonConsecutiveHeight)?,
        anchor.note_count,
        next_count,
        anchor.root,
        CanonicalFaithfulRoot::from_faithful(successor_tree.faithful_root_immutable()),
        block_id,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    struct HybridSigner {
        ed: dregg_types::SigningKey,
        ed_pk: PublicKey,
        pq_pk: MlDsaPublicKey,
        pq: dregg_federation::frost::MlDsaSigningKey,
    }

    impl HybridSigner {
        fn new(seed: u8) -> Self {
            // ML-DSA-65 KeyGen goes through `dregg-pq`, which `process::abort()`s when no verified
            // core is installed — the same install `FaithfulSigner::new` performs in `commit_log`.
            // Without it these four tests SIGABRT'd before reaching a single assertion.
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

        fn sign(&self, record: FaithfulNoteRootRecordV1) -> FaithfulNoteRootEnvelopeV1 {
            let message = record.signing_message();
            FaithfulNoteRootEnvelopeV1 {
                record,
                hybrid_quorum: vec![HybridQuorumSig {
                    pubkey: self.ed_pk,
                    signature: dregg_types::sign(&self.ed, &message),
                    ml_dsa_pubkey: self.pq_pk.0.to_vec(),
                    pq_signature: self.pq.sign(&message).expect("ML-DSA signs"),
                }],
            }
        }
    }

    fn tag(byte: u8) -> [u8; 32] {
        let mut out = [0u8; 32];
        out[0] = byte;
        out
    }

    fn empty_anchor() -> (crate::Poseidon2NoteTree, FaithfulNoteRootAnchorV1) {
        let tree = crate::Poseidon2NoteTree::with_depth(4);
        let root = CanonicalFaithfulRoot::from_faithful(tree.faithful_root_immutable());
        let anchor = FaithfulNoteRootAnchorV1::new(tag(1), tag(2), 7, 40, 0, root).unwrap();
        (tree, anchor)
    }

    fn planned(
        tree: &crate::Poseidon2NoteTree,
        anchor: &FaithfulNoteRootAnchorV1,
        block: u8,
        commitments: &[[u8; 32]],
    ) -> FaithfulNoteRootEnvelopeV1 {
        FaithfulNoteRootEnvelopeV1 {
            record: plan_faithful_note_root_transition_v1(tree, anchor, tag(block), commitments)
                .unwrap(),
            hybrid_quorum: Vec::new(),
        }
    }

    fn signed_planned(
        signer: &HybridSigner,
        tree: &crate::Poseidon2NoteTree,
        anchor: &FaithfulNoteRootAnchorV1,
        block: u8,
        commitments: &[[u8; 32]],
    ) -> FaithfulNoteRootEnvelopeV1 {
        signer.sign(
            plan_faithful_note_root_transition_v1(tree, anchor, tag(block), commitments).unwrap(),
        )
    }

    #[test]
    fn canonical_record_is_exact_and_rejects_malformed_lanes_or_framing() {
        let (tree, anchor) = empty_anchor();
        let envelope = planned(&tree, &anchor, 3, &[[0x41; 32]]);
        let bytes = envelope.record.signing_message();
        assert_eq!(bytes.len(), FAITHFUL_NOTE_ROOT_RECORD_V1_BYTES);
        assert_eq!(&bytes[..8], b"FNHR\x01\x00\x00\x00");
        assert_eq!(bytes[8], 1, "Lean demo layout: session byte 0");
        assert_eq!(bytes[40], 2, "Lean demo layout: federation byte 0");
        assert_eq!(bytes[72], 7, "Lean demo layout: epoch LE");
        assert_eq!(bytes[80], 40, "Lean demo layout: predecessor height LE");
        assert_eq!(bytes[88], 41, "Lean demo layout: successor height LE");
        assert_eq!(bytes[96], 0, "this fixture starts at note count zero");
        assert_eq!(bytes[104], 1, "this fixture appends one note");
        assert_eq!(bytes[176], 3, "Lean demo layout: block id byte 0");
        assert_eq!(
            FaithfulNoteRootRecordV1::from_bytes(&bytes).unwrap(),
            envelope.record
        );
        assert!(FaithfulNoteRootRecordV1::from_bytes(&bytes[..bytes.len() - 1]).is_err());
        let mut trailing = bytes.to_vec();
        trailing.push(0);
        assert!(FaithfulNoteRootRecordV1::from_bytes(&trailing).is_err());
        let mut noncanonical = bytes;
        noncanonical[112..116].copy_from_slice(&BABYBEAR_P.to_le_bytes());
        assert!(matches!(
            FaithfulNoteRootRecordV1::from_bytes(&noncanonical),
            Err(FaithfulNoteRootHistoryError::NonCanonicalRoot { lane: 0, .. })
        ));
    }

    /// Rust correspondence for the Lean `demoAnchor`/`demoRecord` structural
    /// guards: the exact extension accepts, predecessor/session substitution,
    /// replay, and a sibling at the consumed height refuse.
    #[test]
    fn lean_demo_transition_matches_rust_interpreter() {
        let (tree, anchor) = empty_anchor();
        let first = planned(&tree, &anchor, 3, &[[0x11; 32], [0x12; 32]]);
        first.record.validate_extension(&anchor).unwrap();

        let mut history = FaithfulNoteRootHistoryV1::new(anchor.clone());
        history.append_structurally(first.clone()).unwrap();
        assert!(matches!(
            history.append_structurally(first.clone()),
            Err(FaithfulNoteRootHistoryError::Replay)
        ));

        let mut sibling = first.clone();
        sibling.record.block_id = tag(4);
        assert!(history.append_structurally(sibling).is_err());

        let mut wrong_session = first.record.clone();
        wrong_session.session_id = tag(99);
        assert!(matches!(
            wrong_session.validate_extension(&anchor),
            Err(FaithfulNoteRootHistoryError::ContextMismatch("session"))
        ));
    }

    #[test]
    fn planner_binds_exact_live_predecessor_and_multi_append_successor() {
        let (mut tree, anchor) = empty_anchor();
        let commitments = [[0x31; 32], [0x32; 32], [0x33; 32]];
        let record =
            plan_faithful_note_root_transition_v1(&tree, &anchor, tag(3), &commitments).unwrap();
        assert_eq!(record.previous_note_count, 0);
        assert_eq!(record.note_count, 3);
        for commitment in &commitments {
            tree.append_blake3_commitment(commitment);
        }
        assert_eq!(
            record.successor,
            CanonicalFaithfulRoot::from_faithful(tree.faithful_root())
        );

        let mut wrong = anchor;
        wrong.note_count = 1;
        assert!(matches!(
            plan_faithful_note_root_transition_v1(&tree, &wrong, tag(4), &[]),
            Err(FaithfulNoteRootHistoryError::ContextMismatch(
                "live note count"
            ))
        ));
    }

    #[test]
    fn hybrid_api_fails_closed_without_an_enrolled_roster() {
        let (tree, anchor) = empty_anchor();
        let envelope = planned(&tree, &anchor, 3, &[[0x51; 32]]);
        let mut history = FaithfulNoteRootHistoryV1::new(anchor);
        assert!(matches!(
            history.append_hybrid(envelope, &[], &[], 0),
            Err(FaithfulNoteRootHistoryError::AuthenticationFailed)
        ));
        assert!(history.envelopes().is_empty());
    }

    #[test]
    fn durable_hybrid_append_rejects_duplicate_enrolled_pq_keys() {
        let signers = [HybridSigner::new(0xB1), HybridSigner::new(0xB2)];
        let committee = [signers[0].ed_pk, signers[1].ed_pk];
        let enrolled = [signers[0].pq_pk.clone(), signers[1].pq_pk.clone()];
        assert_ne!(committee[0], committee[1]);
        assert_ne!(enrolled[0], enrolled[1]);
        let (tree, anchor) = empty_anchor();
        let record = plan_faithful_note_root_transition_v1(
            &tree,
            &anchor,
            tag(0xB3),
            &[[0xB4; 32]],
        )
        .unwrap();
        let message = record.signing_message();
        let honest = FaithfulNoteRootEnvelopeV1 {
            record: record.clone(),
            hybrid_quorum: signers
                .iter()
                .flat_map(|signer| signer.sign(record.clone()).hybrid_quorum)
                .collect(),
        };

        // The actual durable API admits an honest, distinct two-of-two quorum.
        let good_store = PersistentStore::open_in_memory().unwrap();
        good_store
            .initialize_faithful_note_root_history(&anchor)
            .unwrap();
        good_store
            .append_faithful_note_root_hybrid(&honest, &committee, &enrolled, 2)
            .expect("distinct enrolled hybrid quorum appends");
        let expected = FaithfulNoteRootExpectationV1 {
            records: 1,
            height: record.height,
            note_count: record.note_count,
            root: record.successor,
        };
        let loaded = good_store
            .load_faithful_note_root_history_hybrid(&committee, &enrolled, 2, expected)
            .unwrap();
        assert_eq!(loaded.envelopes(), std::slice::from_ref(&honest));

        // One real PQ signature is reused under two different valid Ed keys.
        // Both halves and both positional pins pass individually; only the
        // enrollment's duplicated PQ authority is invalid.
        let duplicated = [enrolled[0].clone(), enrolled[0].clone()];
        let reused_pq = signers[0].pq.sign(&message).expect("ML-DSA signs");
        let mut aliased = honest.clone();
        for qs in &mut aliased.hybrid_quorum {
            qs.ml_dsa_pubkey = duplicated[0].0.to_vec();
            qs.pq_signature = reused_pq.clone();
        }
        assert_eq!(aliased.hybrid_quorum[0].pq_signature, aliased.hybrid_quorum[1].pq_signature);
        for (qs, enrolled_key) in aliased.hybrid_quorum.iter().zip(&duplicated) {
            assert!(qs.pubkey.verify(&message, &qs.signature));
            assert_eq!(qs.ml_dsa_pubkey.as_slice(), enrolled_key.0.as_slice());
            assert!(enrolled_key.verify(&message, &qs.pq_signature));
        }

        // Use a fresh, empty store: refusal cannot be a replay/height collision
        // with the positive control, and must not mutate either table or seal.
        let refused_store = PersistentStore::open_in_memory().unwrap();
        refused_store
            .initialize_faithful_note_root_history(&anchor)
            .unwrap();
        for threshold in [2, 1] {
            let mut candidate = aliased.clone();
            candidate.hybrid_quorum.truncate(threshold);
            assert!(matches!(
                refused_store.append_faithful_note_root_hybrid(
                    &candidate,
                    &committee,
                    &duplicated,
                    threshold,
                ),
                Err(StoreError::Integrity(message))
                    if message == FaithfulNoteRootHistoryError::AuthenticationFailed.to_string()
            ));
        }
        // Threshold one still rejects: the unused enrollment slot is part of
        // the roster, not a reason to accept shared PQ authority.
        let empty_expected = FaithfulNoteRootExpectationV1 {
            records: 0,
            height: anchor.height,
            note_count: anchor.note_count,
            root: anchor.root,
        };
        let empty = refused_store
            .load_faithful_note_root_history_hybrid(&committee, &enrolled, 2, empty_expected)
            .expect("refused enrollment leaves the installed empty head intact");
        assert!(empty.envelopes().is_empty());
        assert_eq!(empty.head(), anchor);
    }

    #[test]
    fn durable_history_rejects_replay_fork_and_tail_truncation() {
        let store = PersistentStore::open_in_memory().unwrap();
        let (tree, anchor) = empty_anchor();
        store
            .initialize_faithful_note_root_history(&anchor)
            .unwrap();
        let first = planned(&tree, &anchor, 3, &[[0x61; 32]]);
        store.append_faithful_note_root_verified(&first).unwrap();
        assert!(store.append_faithful_note_root_verified(&first).is_err());

        let expected = FaithfulNoteRootExpectationV1 {
            records: 1,
            height: first.record.height,
            note_count: first.record.note_count,
            root: first.record.successor,
        };
        let loaded = store
            .load_faithful_note_root_history_with(expected, |_| true)
            .unwrap();
        assert_eq!(loaded.envelopes().len(), 1);

        // Delete only the tail row while leaving the transactionally written
        // head seal.  Load must reject the apparently valid empty prefix.
        let write = store.db.begin_write().unwrap();
        {
            let mut table = write
                .open_table(tables::FAITHFUL_NOTE_ROOT_HISTORY)
                .unwrap();
            table.remove(first.record.height).unwrap();
        }
        write.commit().unwrap();
        assert!(
            store
                .load_faithful_note_root_history_with(expected, |_| true)
                .is_err()
        );
    }

    #[test]
    fn historical_replay_validates_membership_and_the_complete_later_chain() {
        let store = PersistentStore::open_in_memory().unwrap();
        let (mut tree, anchor) = empty_anchor();
        store
            .initialize_faithful_note_root_history(&anchor)
            .unwrap();

        let first_commitments = [[0x81; 32]];
        let first = planned(&tree, &anchor, 8, &first_commitments);
        for commitment in &first_commitments {
            tree.append_blake3_commitment(commitment);
        }
        let second_anchor = first.record.to_anchor();
        let second = planned(&tree, &second_anchor, 9, &[[0x82; 32]]);
        store.append_faithful_note_root_verified(&first).unwrap();
        store.append_faithful_note_root_verified(&second).unwrap();

        // The first edge is immutable history even though the current seal names the second.
        let write = store.db.begin_write().unwrap();
        append_faithful_note_root_verified_in(&write, &first, Some(&anchor), true).unwrap();
        write.abort().unwrap();

        // Same height is not enough: the exact canonical envelope must be byte-identical.
        let mut wrong = first.clone();
        wrong.record.block_id = tag(10);
        let write = store.db.begin_write().unwrap();
        assert!(matches!(
            append_faithful_note_root_verified_in(&write, &wrong, Some(&anchor), true),
            Err(StoreError::Integrity(ref message)) if message.contains("fork")
        ));
        write.abort().unwrap();

        // Exact historical membership beside a plausible but stale current-head seal is still a
        // corrupt snapshot.  Replay may neither accept it nor rewind the seal to the old edge.
        let write = store.db.begin_write().unwrap();
        {
            let stale_seal = HeadSealV1 {
                records: 2,
                head: first.record.to_anchor(),
            }
            .to_bytes();
            write
                .open_table(tables::METADATA_BYTES)
                .unwrap()
                .insert(tables::META_FAITHFUL_NOTE_ROOT_HEAD, stale_seal.as_slice())
                .unwrap();
        }
        write.commit().unwrap();
        let write = store.db.begin_write().unwrap();
        assert!(matches!(
            append_faithful_note_root_verified_in(&write, &first, Some(&anchor), true),
            Err(StoreError::Integrity(ref message)) if message.contains("persisted head seal")
        ));
        write.abort().unwrap();
    }

    #[test]
    fn direct_historical_authority_authenticates_requested_row_and_sealed_tail() {
        let store = PersistentStore::open_in_memory().unwrap();
        let signer = HybridSigner::new(0x71);
        let (mut tree, anchor) = empty_anchor();
        store
            .initialize_faithful_note_root_history(&anchor)
            .unwrap();

        let first_commitments = [[0x91; 32]];
        let first = signed_planned(&signer, &tree, &anchor, 9, &first_commitments);
        for commitment in &first_commitments {
            tree.append_blake3_commitment(commitment);
        }
        let second = signed_planned(&signer, &tree, &first.record.to_anchor(), 10, &[[0x92; 32]]);
        store.append_faithful_note_root_verified(&first).unwrap();
        store.append_faithful_note_root_verified(&second).unwrap();

        let committee = [signer.ed_pk];
        let pq_committee = [signer.pq_pk.clone()];
        let authority = store
            .store_authenticated_historical_root_hybrid(
                &committee,
                &pq_committee,
                1,
                first.record.height,
                first.record.successor.to_bytes(),
            )
            .unwrap()
            .expect("direct signed historical row");
        assert_eq!(authority.height(), first.record.height);
        assert_eq!(authority.root(), first.record.successor);
        assert!(
            store
                .store_authenticated_historical_root_hybrid(
                    &committee,
                    &pq_committee,
                    1,
                    first.record.height,
                    anchor.root.to_bytes(),
                )
                .unwrap()
                .is_none(),
            "the right height with a substituted root is not authority"
        );
    }

    #[test]
    fn direct_historical_authority_rejects_forged_row_and_stale_head_seal() {
        let store = PersistentStore::open_in_memory().unwrap();
        let signer = HybridSigner::new(0x72);
        let (mut tree, anchor) = empty_anchor();
        store
            .initialize_faithful_note_root_history(&anchor)
            .unwrap();

        let first_commitments = [[0xa1; 32]];
        let first = signed_planned(&signer, &tree, &anchor, 11, &first_commitments);
        for commitment in &first_commitments {
            tree.append_blake3_commitment(commitment);
        }
        let second = signed_planned(&signer, &tree, &first.record.to_anchor(), 12, &[[0xa2; 32]]);
        store.append_faithful_note_root_verified(&first).unwrap();
        store.append_faithful_note_root_verified(&second).unwrap();

        let committee = [signer.ed_pk];
        let pq_committee = [signer.pq_pk.clone()];
        let mut forged = first.clone();
        forged.hybrid_quorum[0].pq_signature[0] ^= 1;
        let write = store.db.begin_write().unwrap();
        {
            let mut table = write
                .open_table(tables::FAITHFUL_NOTE_ROOT_HISTORY)
                .unwrap();
            let bytes = forged.to_bytes().unwrap();
            table.insert(first.record.height, bytes.as_slice()).unwrap();
        }
        write.commit().unwrap();
        assert!(
            store
                .store_authenticated_historical_root_hybrid(
                    &committee,
                    &pq_committee,
                    1,
                    first.record.height,
                    first.record.successor.to_bytes(),
                )
                .unwrap()
                .is_none(),
            "a forged direct row cannot mint store authority"
        );

        // A genuine but stale signed row rekeyed under another height retains
        // valid signature bytes.  Direct index admission still refuses because
        // the signed height must equal the lookup key.
        let write = store.db.begin_write().unwrap();
        {
            let mut table = write
                .open_table(tables::FAITHFUL_NOTE_ROOT_HISTORY)
                .unwrap();
            let stale_bytes = second.to_bytes().unwrap();
            table
                .insert(first.record.height, stale_bytes.as_slice())
                .unwrap();
        }
        write.commit().unwrap();
        assert!(
            store
                .store_authenticated_historical_root_hybrid(
                    &committee,
                    &pq_committee,
                    1,
                    first.record.height,
                    first.record.successor.to_bytes(),
                )
                .unwrap()
                .is_none(),
            "a valid stale row under the wrong height cannot mint authority"
        );

        // Restore the signed row, then leave the two-row table beside a head
        // seal rolled back to the first edge.  Exact count/span/head-to-tail
        // agreement must reject the stale seal without replaying the history.
        let write = store.db.begin_write().unwrap();
        {
            let mut table = write
                .open_table(tables::FAITHFUL_NOTE_ROOT_HISTORY)
                .unwrap();
            let first_bytes = first.to_bytes().unwrap();
            table
                .insert(first.record.height, first_bytes.as_slice())
                .unwrap();
            let stale = HeadSealV1 {
                records: 2,
                head: first.record.to_anchor(),
            }
            .to_bytes();
            let mut metadata = write.open_table(tables::METADATA_BYTES).unwrap();
            metadata
                .insert(tables::META_FAITHFUL_NOTE_ROOT_HEAD, stale.as_slice())
                .unwrap();
        }
        write.commit().unwrap();
        assert!(
            store
                .store_authenticated_historical_root_hybrid(
                    &committee,
                    &pq_committee,
                    1,
                    first.record.height,
                    first.record.successor.to_bytes(),
                )
                .is_err()
        );
    }

    #[test]
    fn direct_historical_authority_is_membership_equivalent_to_full_replay() {
        let store = PersistentStore::open_in_memory().unwrap();
        let signer = HybridSigner::new(0x74);
        let (mut tree, anchor) = empty_anchor();
        store
            .initialize_faithful_note_root_history(&anchor)
            .unwrap();
        let mut head = anchor.clone();
        for (block, commitment) in [(14, [0xc1; 32]), (15, [0xc2; 32]), (16, [0xc3; 32])] {
            let envelope = signed_planned(&signer, &tree, &head, block, &[commitment]);
            tree.append_blake3_commitment(&commitment);
            store.append_faithful_note_root_verified(&envelope).unwrap();
            head = envelope.record.to_anchor();
        }

        let committee = [signer.ed_pk];
        let pq_committee = [signer.pq_pk.clone()];
        let expected = store.faithful_note_root_expectation().unwrap().unwrap();
        let replayed = store
            .load_faithful_note_root_history_hybrid(&committee, &pq_committee, 1, expected)
            .unwrap();
        let mut members = vec![(replayed.anchor().height, replayed.anchor().root.to_bytes())];
        members.extend(
            replayed
                .envelopes()
                .iter()
                .map(|envelope| (envelope.record.height, envelope.record.successor.to_bytes())),
        );
        for (height, root) in members {
            assert!(
                store
                    .store_authenticated_historical_root_hybrid(
                        &committee,
                        &pq_committee,
                        1,
                        height,
                        root,
                    )
                    .unwrap()
                    .is_some(),
                "every full-replay member has direct authority"
            );
        }
        assert!(
            store
                .store_authenticated_historical_root_hybrid(
                    &committee,
                    &pq_committee,
                    1,
                    replayed.envelopes()[0].record.height,
                    anchor.root.to_bytes(),
                )
                .unwrap()
                .is_none()
        );
        assert!(
            store
                .store_authenticated_historical_root_hybrid(
                    &committee,
                    &pq_committee,
                    1,
                    head.height + 1,
                    head.root.to_bytes(),
                )
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn direct_historical_authority_survives_restart() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("history.redb");
        let signer = HybridSigner::new(0x73);
        let (tree, anchor) = empty_anchor();
        let first = signed_planned(&signer, &tree, &anchor, 13, &[[0xb1; 32]]);
        {
            let store = PersistentStore::open(&path).unwrap();
            store
                .initialize_faithful_note_root_history(&anchor)
                .unwrap();
            store.append_faithful_note_root_verified(&first).unwrap();
        }

        let reopened = PersistentStore::open(&path).unwrap();
        let committee = [signer.ed_pk];
        let pq_committee = [signer.pq_pk.clone()];
        assert!(
            reopened
                .store_authenticated_historical_root_hybrid(
                    &committee,
                    &pq_committee,
                    1,
                    first.record.height,
                    first.record.successor.to_bytes(),
                )
                .unwrap()
                .is_some()
        );
    }

    /// The replay checks signatures on several threads but must refuse exactly
    /// as a serial row-by-row loop does: at the first failing row in key order,
    /// with every earlier row checked, and an undecodable later row never masks
    /// an earlier authentication failure.
    #[test]
    fn parallel_replay_refuses_at_the_first_failing_row_in_key_order() {
        let store = PersistentStore::open_in_memory().unwrap();
        let (mut tree, anchor) = empty_anchor();
        store
            .initialize_faithful_note_root_history(&anchor)
            .unwrap();
        let mut head = anchor;
        let mut heights = Vec::new();
        for block in 0x20..0x40u8 {
            let commitment = [block; 32];
            let envelope = planned(&tree, &head, block, &[commitment]);
            tree.append_blake3_commitment(&commitment);
            store.append_faithful_note_root_verified(&envelope).unwrap();
            head = envelope.record.to_anchor();
            heights.push(envelope.record.height);
        }
        let expected = store.faithful_note_root_expectation().unwrap().unwrap();
        let loaded = store
            .load_faithful_note_root_history_with(expected, |_| true)
            .unwrap();
        assert_eq!(loaded.envelopes().len(), heights.len());

        let bad = heights[9];
        let checked = std::sync::Mutex::new(std::collections::BTreeSet::new());
        let refusal = store
            .load_faithful_note_root_history_with(expected, |envelope| {
                checked.lock().unwrap().insert(envelope.record.height);
                envelope.record.height != bad
            })
            .unwrap_err();
        let authentication = integrity(FaithfulNoteRootHistoryError::AuthenticationFailed);
        assert_eq!(refusal.to_string(), authentication.to_string());
        let checked = checked.into_inner().unwrap();
        assert!(heights[..=9].iter().all(|height| checked.contains(height)));

        // Corrupt a LATER row: the earlier authentication failure still decides.
        let write = store.db.begin_write().unwrap();
        {
            let mut table = write
                .open_table(tables::FAITHFUL_NOTE_ROOT_HISTORY)
                .unwrap();
            table.insert(heights[20], [0xFFu8; 3].as_slice()).unwrap();
        }
        write.commit().unwrap();
        let refusal = store
            .load_faithful_note_root_history_with(expected, |envelope| {
                envelope.record.height != bad
            })
            .unwrap_err();
        assert_eq!(refusal.to_string(), authentication.to_string());
        // With every row authentic, the corrupt row is the refusal.
        let refusal = store
            .load_faithful_note_root_history_with(expected, |_| true)
            .unwrap_err();
        assert_ne!(refusal.to_string(), authentication.to_string());
    }

    fn seal_quorum(signer: &HybridSigner, statement: &[u8]) -> Vec<HybridQuorumSig> {
        vec![HybridQuorumSig {
            pubkey: signer.ed_pk,
            signature: dregg_types::sign(&signer.ed, statement),
            ml_dsa_pubkey: signer.pq_pk.0.to_vec(),
            pq_signature: signer.pq.sign(statement).expect("ML-DSA signs"),
        }]
    }

    /// Load with the real hybrid checks, counting the per-row ones.
    fn audited_load(
        store: &PersistentStore,
        signer: &HybridSigner,
    ) -> (StoreResult<AuthenticatedFaithfulNoteRootPrefix>, usize) {
        let committee = [signer.ed_pk];
        let pq_committee = [signer.pq_pk.clone()];
        let checked = std::sync::atomic::AtomicUsize::new(0);
        let expected = store.faithful_note_root_expectation().unwrap().unwrap();
        let loaded = store
            .load_faithful_note_root_history_audited_with(
                expected,
                faithful_note_root_audit_policy(&committee, &pq_committee, 1),
                |envelope| {
                    checked.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    envelope.verify_hybrid(&committee, &pq_committee, 1)
                },
                |statement, quorum| {
                    dregg_federation::receipt::verify_hybrid_quorum_sigs(
                        quorum,
                        statement,
                        &committee,
                        &pq_committee,
                        1,
                    )
                },
            )
            .map(|(_, prefix)| prefix);
        (loaded, checked.into_inner())
    }

    #[test]
    fn audit_policy_never_promotes_a_weaker_minted_prefix() {
        let store = PersistentStore::open_in_memory().unwrap();
        let signers = [0x77, 0x78, 0x79].map(HybridSigner::new);
        let committee = signers.each_ref().map(|signer| signer.ed_pk);
        let pq_committee = signers.each_ref().map(|signer| signer.pq_pk.clone());
        let (tree, anchor) = empty_anchor();
        store.initialize_faithful_note_root_history(&anchor).unwrap();
        let envelope = signed_planned(&signers[0], &tree, &anchor, 0x36, &[[0x36; 32]]);
        assert!(envelope.verify_hybrid(&committee, &pq_committee, 1));
        assert!(!envelope.verify_hybrid(&committee, &pq_committee, 3));
        store.append_faithful_note_root_verified(&envelope).unwrap();
        let expected = store.faithful_note_root_expectation().unwrap().unwrap();
        let (_, prefix) = store
            .load_faithful_note_root_history_hybrid_audited(&committee, &pq_committee, 1, expected)
            .unwrap();
        let quorum: Vec<HybridQuorumSig> = signers
            .iter()
            .flat_map(|signer| seal_quorum(signer, prefix.statement()))
            .collect();
        assert!(dregg_federation::receipt::verify_hybrid_quorum_sigs(
            &quorum, prefix.statement(), &committee, &pq_committee, 3,
        ));
        store.store_faithful_note_root_audit_seal(&prefix, quorum).unwrap();
        let refusal = store
            .load_faithful_note_root_history_hybrid(&committee, &pq_committee, 3, expected)
            .unwrap_err();
        assert_eq!(
            refusal.to_string(),
            integrity(FaithfulNoteRootHistoryError::AuthenticationFailed).to_string()
        );
        for threshold in [0, 3, 4] {
            let refusal = store
                .load_faithful_note_root_history_hybrid_audited(&committee, &pq_committee, threshold, expected)
                .unwrap_err();
            assert_eq!(
                refusal.to_string(),
                integrity(FaithfulNoteRootHistoryError::AuthenticationFailed).to_string()
            );
        }
        let (_, healthy) = store
            .load_faithful_note_root_history_hybrid_audited(&committee, &pq_committee, 1, expected)
            .unwrap();
        assert_eq!(healthy.sealed_records(), 1);
        let mut reordered = committee;
        let mut reordered_pq = pq_committee.clone();
        reordered.reverse();
        reordered_pq.reverse();
        let (_, rechecked) = store
            .load_faithful_note_root_history_hybrid_audited(&reordered, &reordered_pq, 1, expected)
            .unwrap();
        assert_eq!(rechecked.sealed_records(), 0);
        let mut substituted_pq = pq_committee.clone();
        substituted_pq.swap(0, 1);
        assert!(store
            .load_faithful_note_root_history_hybrid_audited(&committee, &substituted_pq, 1, expected)
            .is_err());
        store
            .store_faithful_note_root_audit_seal(&prefix, seal_quorum(&signers[0], prefix.statement()))
            .unwrap();
        let replacement = HybridSigner::new(0x7a);
        let replaced = [committee[0], committee[1], replacement.ed_pk];
        let replaced_pq = [pq_committee[0].clone(), pq_committee[1].clone(), replacement.pq_pk.clone()];
        let (_, rechecked) = store
            .load_faithful_note_root_history_hybrid_audited(&replaced, &replaced_pq, 1, expected)
            .unwrap();
        assert_eq!(rechecked.sealed_records(), 0);
        // A duplicated roster is refused during row authentication by
        // `federation::receipt::verify_hybrid_quorum_sigs` (task/4721), so no
        // `policy: None` prefix is minted here and the seal guard is
        // unreachable.  See the retired arm further down this module.
    }

    #[test]
    fn audit_policy_value_identity_and_invalid_descriptors() {
        let signers = [0x7b, 0x7c, 0x7d].map(HybridSigner::new);
        let committee = signers.each_ref().map(|signer| signer.ed_pk);
        let pq_committee = signers.each_ref().map(|signer| signer.pq_pk.clone());
        let policy = faithful_note_root_audit_policy(&committee, &pq_committee, 1).unwrap();
        assert_ne!(Some(policy), faithful_note_root_audit_policy(&committee, &pq_committee, 2));
        let mut repeated_pq = pq_committee.clone();
        repeated_pq[1] = repeated_pq[0].clone();
        assert_ne!(Some(policy), faithful_note_root_audit_policy(&committee, &repeated_pq, 1));
        assert!(faithful_note_root_audit_policy(&committee, &pq_committee[..2], 1).is_none());
        assert!(faithful_note_root_audit_policy(&[], &[], 1).is_none());
        assert!(faithful_note_root_audit_policy(&committee, &pq_committee, 0).is_none());
        assert!(faithful_note_root_audit_policy(&committee, &pq_committee, 4).is_none());
        let duplicated = [committee[0], committee[0], committee[2]];
        let duplicated_pq = [pq_committee[0].clone(), pq_committee[0].clone(), pq_committee[2].clone()];
        assert!(faithful_note_root_audit_policy(&duplicated, &duplicated_pq, 1).is_none());
    }

    #[test]
    fn policy_bound_audit_survives_reopen_and_legacy_seal_falls_back() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("audit-policy.redb");
        let signer = HybridSigner::new(0x7e);
        let (tree, anchor) = empty_anchor();
        let envelope = signed_planned(&signer, &tree, &anchor, 0x39, &[[0x39; 32]]);
        let legacy = {
            let store = PersistentStore::open(&path).unwrap();
            store.initialize_faithful_note_root_history(&anchor).unwrap();
            store.append_faithful_note_root_verified(&envelope).unwrap();
            let (prefix, checked) = audited_load(&store, &signer);
            let prefix = prefix.unwrap();
            assert_eq!((prefix.records(), prefix.sealed_records(), checked), (1, 0, 1));
            store
                .store_faithful_note_root_audit_seal(&prefix, seal_quorum(&signer, prefix.statement()))
                .unwrap();
            let mut statement = prefix.statement()[..176].to_vec();
            statement[4..6].copy_from_slice(&VERSION_V1.to_le_bytes());
            let hybrid_quorum = seal_quorum(&signer, &statement);
            postcard::to_stdvec(&AuditSealWireV1 {
                version: VERSION_V1,
                statement,
                hybrid_quorum,
            })
            .unwrap()
        };
        let reopened = PersistentStore::open(&path).unwrap();
        let (prefix, checked) = audited_load(&reopened, &signer);
        assert_eq!((prefix.unwrap().sealed_records(), checked), (1, 0));
        assert!(FaithfulNoteRootAuditSealV1::from_bytes(&legacy).is_none());
        let write = reopened.db.begin_write().unwrap();
        {
            let mut metadata = write.open_table(tables::METADATA_BYTES).unwrap();
            metadata.insert(tables::META_FAITHFUL_NOTE_ROOT_AUDIT, legacy.as_slice()).unwrap();
        }
        write.commit().unwrap();
        let (prefix, checked) = audited_load(&reopened, &signer);
        assert_eq!((prefix.unwrap().sealed_records(), checked), (0, 1));
    }

    /// Build a one-row history whose row is signed by `signers[0]` and return
    /// the store plus the exact expectation a load must meet.  The controls
    /// below drive only the PUBLIC audited API, so the same test bodies compile
    /// and run against the pre-cure tree, which is what makes their RED capture
    /// (the old code accepting) meaningful rather than a compile error.
    fn one_row_history(
        signers: &[HybridSigner],
        block: u8,
    ) -> (PersistentStore, FaithfulNoteRootExpectationV1) {
        let store = PersistentStore::open_in_memory().unwrap();
        let (tree, anchor) = empty_anchor();
        store
            .initialize_faithful_note_root_history(&anchor)
            .unwrap();
        let row = signed_planned(&signers[0], &tree, &anchor, block, &[[block; 32]]);
        store.append_faithful_note_root_verified(&row).unwrap();
        let expected = store.faithful_note_root_expectation().unwrap().unwrap();
        (store, expected)
    }

    /// Control (weak mint 1 / strong seal 3): a seal minted while the row was
    /// authenticated under a 1-of-3 policy must NOT authenticate that row when
    /// the audited load runs under a 3-of-3 policy, even though a genuine 3-of-3
    /// quorum signs the statement.  The old statement bound no policy, so it was
    /// honoured; the cure binds the mint policy, so the row is re-checked and
    /// refused under the stronger policy it was never minted under.
    #[test]
    fn strong_seal_does_not_authenticate_a_row_minted_under_a_weaker_policy() {
        let signers = [0x81, 0x82, 0x83].map(HybridSigner::new);
        let committee = signers.each_ref().map(|signer| signer.ed_pk);
        let pq_committee = signers.each_ref().map(|signer| signer.pq_pk.clone());
        let store = PersistentStore::open_in_memory().unwrap();
        let (tree, anchor) = empty_anchor();
        store
            .initialize_faithful_note_root_history(&anchor)
            .unwrap();
        let row = signed_planned(&signers[0], &tree, &anchor, 0x81, &[[0x81; 32]]);
        assert!(
            row.verify_hybrid(&committee, &pq_committee, 1),
            "row mints under threshold 1"
        );
        assert!(
            !row.verify_hybrid(&committee, &pq_committee, 3),
            "row is NOT a 3-of-3 row"
        );
        store.append_faithful_note_root_verified(&row).unwrap();
        let expected = store.faithful_note_root_expectation().unwrap().unwrap();

        // Mint the prefix (and so the policy the seal binds) under the WEAK policy.
        let (_, prefix) = store
            .load_faithful_note_root_history_hybrid_audited(&committee, &pq_committee, 1, expected)
            .unwrap();
        assert_eq!(prefix.sealed_records(), 0);
        // A STRONG 3-of-3 quorum over exactly that statement: real signers.
        let strong: Vec<HybridQuorumSig> = signers
            .iter()
            .flat_map(|signer| seal_quorum(signer, prefix.statement()))
            .collect();
        assert!(dregg_federation::receipt::verify_hybrid_quorum_sigs(
            &strong,
            prefix.statement(),
            &committee,
            &pq_committee,
            3,
        ));
        store
            .store_faithful_note_root_audit_seal(&prefix, strong)
            .unwrap();

        // Honoured for the policy it was minted under...
        let (_, honored) = store
            .load_faithful_note_root_history_hybrid_audited(&committee, &pq_committee, 1, expected)
            .unwrap();
        assert_eq!(honored.sealed_records(), 1);
        // ...but it must NOT cover the row under the stronger policy.
        let refusal = store
            .load_faithful_note_root_history_hybrid_audited(&committee, &pq_committee, 3, expected)
            .unwrap_err();
        assert_eq!(
            refusal.to_string(),
            integrity(FaithfulNoteRootHistoryError::AuthenticationFailed).to_string()
        );
    }

    /// Control (roster reorder / member change / PQ change): a seal is minted
    /// under one exact ordered enrollment.  Loading under any other roster --
    /// reordered, a replaced member, or a changed PQ key for a member that did
    /// not sign the row (so the seal's own quorum still verifies) -- must NOT let
    /// that seal cover the row.  The row is re-checked, so the load still
    /// succeeds but reports `sealed_records() == 0`.
    #[test]
    fn seal_does_not_carry_to_a_different_enrollment() {
        let signers = [0x84, 0x85, 0x86].map(HybridSigner::new);
        let committee = signers.each_ref().map(|signer| signer.ed_pk);
        let pq_committee = signers.each_ref().map(|signer| signer.pq_pk.clone());
        let (store, expected) = one_row_history(&signers, 0x84);
        let (_, prefix) = store
            .load_faithful_note_root_history_hybrid_audited(&committee, &pq_committee, 1, expected)
            .unwrap();
        store
            .store_faithful_note_root_audit_seal(
                &prefix,
                seal_quorum(&signers[0], prefix.statement()),
            )
            .unwrap();
        // Sanity: the exact roster the seal was minted under still honours it.
        let (_, same) = store
            .load_faithful_note_root_history_hybrid_audited(&committee, &pq_committee, 1, expected)
            .unwrap();
        assert_eq!(same.sealed_records(), 1);

        // (a) Reordered roster: same members, different order.
        let reordered = [committee[2], committee[1], committee[0]];
        let reordered_pq = [
            pq_committee[2].clone(),
            pq_committee[1].clone(),
            pq_committee[0].clone(),
        ];
        let (_, reordered_prefix) = store
            .load_faithful_note_root_history_hybrid_audited(&reordered, &reordered_pq, 1, expected)
            .unwrap();
        assert_eq!(reordered_prefix.sealed_records(), 0);

        // (b) A replaced member (the replacement did not sign the row).
        let replacement = HybridSigner::new(0x87);
        let replaced = [committee[0], committee[1], replacement.ed_pk];
        let replaced_pq = [
            pq_committee[0].clone(),
            pq_committee[1].clone(),
            replacement.pq_pk.clone(),
        ];
        let (_, replaced_prefix) = store
            .load_faithful_note_root_history_hybrid_audited(&replaced, &replaced_pq, 1, expected)
            .unwrap();
        assert_eq!(replaced_prefix.sealed_records(), 0);

        // (c) Same members, changed PQ enrollment for a NON-signer: the seal's
        // quorum still verifies, so only the bound policy can catch the swap.
        let changed = HybridSigner::new(0x88);
        let changed_pq = [
            pq_committee[0].clone(),
            pq_committee[1].clone(),
            changed.pq_pk.clone(),
        ];
        let (_, changed_prefix) = store
            .load_faithful_note_root_history_hybrid_audited(&committee, &changed_pq, 1, expected)
            .unwrap();
        assert_eq!(changed_prefix.sealed_records(), 0);
    }

    // RETIRED (task/4180).  This arm asserted that a roster which cannot define
    // a cache policy (a duplicated classical identity) still authenticates its
    // rows, so only `store_faithful_note_root_audit_seal`'s `policy.is_none()`
    // check kept its prefix unsealable.  That premise is refuted on
    // `origin/main`: a duplicated enrolled roster is refused during row
    // authentication, before a `policy: None` prefix can be minted, by
    // `federation::receipt::verify_hybrid_quorum_sigs` (task/4721, 0da3639f8),
    // whose whole-roster PQ-distinctness guard the arms' `[pq0, pq0, pq2]`
    // trips; a duplicated CLASSICAL identity with distinct PQ slots trips its
    // enrolled-index pin instead (the collided `index_of` resolves the signer
    // to the later slot's key, so the PQ half fails).  Every input
    // that makes `faithful_note_root_audit_policy` return `None` (threshold 0,
    // threshold > len, length mismatch, duplicated classical) is refused the
    // same way, so the property is subsumed: no public-API input reaches the
    // seal guard.  The policy's `None` set stays covered by
    // `audit_policy_value_identity_and_invalid_descriptors`; the roster
    // refusals by `federation::receipt::hybrid_quorum_rejects_duplicate_
    // enrolled_pq_keys` (task/4721), the `verify_pq_quorum_half` controls
    // (task/4847), and `durable_hybrid_append_rejects_duplicate_enrolled_pq_keys`
    // here.  The `store_faithful_note_root_audit_seal` guard itself now has no
    // test: nothing can reach it from the public API.

    /// Control (reopen + legacy seal): a version-1 seal written to disk must be
    /// ignored after a reopen, so every row is re-authenticated.  The old reader
    /// accepted the v1 statement and skipped the row across the reopen.
    #[test]
    fn legacy_seal_does_not_survive_a_reopen_as_cache_evidence() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("legacy-audit-policy.redb");
        let signer = HybridSigner::new(0x8c);
        let (tree, anchor) = empty_anchor();
        let row = signed_planned(&signer, &tree, &anchor, 0x8c, &[[0x8c; 32]]);
        {
            let store = PersistentStore::open(&path).unwrap();
            store
                .initialize_faithful_note_root_history(&anchor)
                .unwrap();
            store.append_faithful_note_root_verified(&row).unwrap();
            let expected = store.faithful_note_root_expectation().unwrap().unwrap();
            let committee = [signer.ed_pk];
            let pq_committee = [signer.pq_pk.clone()];
            let (_, prefix) = store
                .load_faithful_note_root_history_hybrid_audited(
                    &committee,
                    &pq_committee,
                    1,
                    expected,
                )
                .unwrap();
            assert_eq!(prefix.sealed_records(), 0);
            // Hand-write a LEGACY version-1 seal over that statement: the first
            // 176 bytes carry the anchor/records/digest the old reader accepted.
            let mut statement = prefix.statement()[..176].to_vec();
            statement[4..6].copy_from_slice(&VERSION_V1.to_le_bytes());
            let hybrid_quorum = seal_quorum(&signer, &statement);
            let bytes = postcard::to_stdvec(&AuditSealWireV1 {
                version: VERSION_V1,
                statement,
                hybrid_quorum,
            })
            .unwrap();
            let write = store.db.begin_write().unwrap();
            {
                let mut metadata = write.open_table(tables::METADATA_BYTES).unwrap();
                metadata
                    .insert(tables::META_FAITHFUL_NOTE_ROOT_AUDIT, bytes.as_slice())
                    .unwrap();
            }
            write.commit().unwrap();
        }
        let reopened = PersistentStore::open(&path).unwrap();
        let expected = reopened.faithful_note_root_expectation().unwrap().unwrap();
        let (history, prefix) = reopened
            .load_faithful_note_root_history_hybrid_audited(
                &[signer.ed_pk],
                &[signer.pq_pk.clone()],
                1,
                expected,
            )
            .unwrap();
        assert_eq!(history.envelopes().len(), 1);
        assert_eq!(
            prefix.sealed_records(),
            0,
            "the legacy seal must not cover the row"
        );
    }

    /// An audit seal from the row roster stands in for the per-row checks of
    /// exactly the rows it names; rows appended later are still checked, and a
    /// row edited under the seal, or a seal from another key, is not trusted.
    #[test]
    fn audit_seal_skips_only_the_rows_it_authenticates() {
        let store = PersistentStore::open_in_memory().unwrap();
        let signer = HybridSigner::new(0x75);
        let stranger = HybridSigner::new(0x76);
        let (mut tree, anchor) = empty_anchor();
        store
            .initialize_faithful_note_root_history(&anchor)
            .unwrap();
        let mut head = anchor;
        let mut envelopes = Vec::new();
        let mut append = |store: &PersistentStore, block: u8| {
            let commitment = [block; 32];
            let envelope = signed_planned(&signer, &tree, &head, block, &[commitment]);
            tree.append_blake3_commitment(&commitment);
            store.append_faithful_note_root_verified(&envelope).unwrap();
            head = envelope.record.to_anchor();
            envelopes.push(envelope);
        };
        for block in 0x30..0x33 {
            append(&store, block);
        }

        let (prefix, checked) = audited_load(&store, &signer);
        let prefix = prefix.unwrap();
        assert_eq!((prefix.records(), prefix.sealed_records(), checked), (3, 0, 3));
        store
            .store_faithful_note_root_audit_seal(&prefix, seal_quorum(&signer, prefix.statement()))
            .unwrap();
        for block in 0x33..0x35 {
            append(&store, block);
        }
        let (prefix, checked) = audited_load(&store, &signer);
        let prefix = prefix.unwrap();
        assert_eq!((prefix.records(), prefix.sealed_records(), checked), (5, 3, 2));
        assert_eq!(
            store
                .load_faithful_note_root_history_hybrid(
                    &[signer.ed_pk],
                    &[signer.pq_pk.clone()],
                    1,
                    store.faithful_note_root_expectation().unwrap().unwrap(),
                )
                .unwrap()
                .envelopes()
                .len(),
            5
        );

        // A seal signed by a key outside the roster is ignored.
        store
            .store_faithful_note_root_audit_seal(&prefix, seal_quorum(&stranger, prefix.statement()))
            .unwrap();
        let (prefix, checked) = audited_load(&store, &signer);
        let prefix = prefix.unwrap();
        assert_eq!((prefix.sealed_records(), checked), (0, 5));

        // Re-sign one sealed row with another key: its bytes no longer match
        // the seal's digest, so it is checked, and refused.
        store
            .store_faithful_note_root_audit_seal(&prefix, seal_quorum(&signer, prefix.statement()))
            .unwrap();
        assert_eq!(audited_load(&store, &signer).0.unwrap().sealed_records(), 5);
        let forged = stranger.sign(envelopes[1].record.clone());
        let write = store.db.begin_write().unwrap();
        {
            let mut table = write
                .open_table(tables::FAITHFUL_NOTE_ROOT_HISTORY)
                .unwrap();
            table
                .insert(forged.record.height, forged.to_bytes().unwrap().as_slice())
                .unwrap();
        }
        write.commit().unwrap();
        let (refusal, _) = audited_load(&store, &signer);
        assert_eq!(
            refusal.unwrap_err().to_string(),
            integrity(FaithfulNoteRootHistoryError::AuthenticationFailed).to_string()
        );
    }

    #[test]
    fn exact_expectation_rejects_a_valid_prefix() {
        let (tree, anchor) = empty_anchor();
        let first = planned(&tree, &anchor, 3, &[[0x71; 32]]);
        let mut history = FaithfulNoteRootHistoryV1::new(anchor.clone());
        history.append_structurally(first.clone()).unwrap();
        let full = FaithfulNoteRootExpectationV1 {
            records: 1,
            height: first.record.height,
            note_count: first.record.note_count,
            root: first.record.successor,
        };
        history.verify_exact_snapshot(full).unwrap();
        assert!(
            FaithfulNoteRootHistoryV1::new(anchor)
                .verify_exact_snapshot(full)
                .is_err()
        );
    }
}
