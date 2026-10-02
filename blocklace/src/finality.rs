//! Core blocklace data structure: a DAG of signed blocks with equivocation detection.
//!
//! Based on arXiv:2402.08068. The blocklace is a partially-ordered set of signed
//! blocks, where each block contains hash-pointers to its predecessors. Each
//! participant maintains a local view that grows monotonically via CRDT union-merge.

use std::collections::{HashMap, HashSet, VecDeque};

use ed25519_dalek::{Signer, SigningKey, VerifyingKey};
use serde::{Deserialize, Serialize};

// ─── Core Types ──────────────────────────────────────────────────────────────

/// A block identity: the blake3 hash of the signed content.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct BlockId(pub [u8; 32]);

impl std::fmt::Debug for BlockId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "BlockId({})",
            self.0[..4]
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>()
        )
    }
}

impl std::fmt::Display for BlockId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.0[..8]
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>()
        )
    }
}

/// The payload carried by a block.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Payload {
    /// A dregg turn (serialized state transition).
    Turn(Vec<u8>),
    /// A dregg turn plus devnet material produced at commit time.
    ///
    /// The blocklace remains payload-semantic agnostic: these fields are
    /// opaque bytes here and decoded by the node/explorer layer. Keeping raw
    /// `Turn` alongside this variant preserves compatibility with older
    /// blocks and peers that only carry signed turn bytes.
    TurnBundle(TurnArtifactBundle),
    /// Flag-day turn carrier with consensus-authenticated time.
    ///
    /// The timestamp is part of [`Block::payload_bytes`], hence both signature halves and the block
    /// id commit to it. Legacy [`Payload::Turn`] / [`Payload::TurnBundle`] remain decodable for
    /// historical replay but are refused by a lace with consensus-time-v1 enabled.
    ConsensusTimedTurnV1(ConsensusTimedTurnPayloadV1),
    /// An acknowledgment (I've seen these blocks).
    Ack,
    /// A checkpoint (federation root at this height).
    Checkpoint { root: [u8; 32], height: u64 },
    /// A membership vote (join/leave).
    MembershipVote { action: MembershipAction },
    /// Generic application data.
    Data(Vec<u8>),
}

const CONSENSUS_TIME_MAGIC_V1: [u8; 4] = *b"CTM1";
const CONSENSUS_TIME_VERSION_V1: u8 = 1;
/// Exact canonical width of a consensus-time-v1 claim.
pub const CONSENSUS_TIME_V1_WIRE_LEN: usize = 16;
/// Protocol-wide maximum causal time advance between a timed turn and its predecessor frontier.
///
/// This is a validity bound, not a fair-clock oracle: CTM1 permits a producer to choose any value
/// in the interval, including the maximum on every turn. Deployments must label it as causal replay
/// time (the devnet mode does); federation wall time needs a quorum median/beacon or exact round
/// schedule in a later policy version.
pub const CONSENSUS_TIME_V1_MAX_FORWARD_SECONDS: i64 = 300;

/// Fixed-width authenticated consensus time carried by a versioned turn payload.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConsensusTimeV1 {
    unix_seconds: i64,
}

impl ConsensusTimeV1 {
    pub const fn new(unix_seconds: i64) -> Self {
        Self { unix_seconds }
    }

    pub const fn unix_seconds(self) -> i64 {
        self.unix_seconds
    }

    pub fn encode(self) -> [u8; CONSENSUS_TIME_V1_WIRE_LEN] {
        let mut out = [0u8; CONSENSUS_TIME_V1_WIRE_LEN];
        out[..4].copy_from_slice(&CONSENSUS_TIME_MAGIC_V1);
        out[4] = CONSENSUS_TIME_VERSION_V1;
        out[8..].copy_from_slice(&self.unix_seconds.to_le_bytes());
        out
    }

    pub fn decode(bytes: &[u8]) -> Result<Self, ConsensusTimeWireError> {
        if bytes.len() != CONSENSUS_TIME_V1_WIRE_LEN {
            return Err(ConsensusTimeWireError::Length(bytes.len()));
        }
        if bytes[..4] != CONSENSUS_TIME_MAGIC_V1 {
            return Err(ConsensusTimeWireError::Magic);
        }
        if bytes[4] != CONSENSUS_TIME_VERSION_V1 {
            return Err(ConsensusTimeWireError::Version(bytes[4]));
        }
        if bytes[5..8] != [0; 3] {
            return Err(ConsensusTimeWireError::Reserved);
        }
        Ok(Self::new(i64::from_le_bytes(
            bytes[8..].try_into().expect("eight bytes"),
        )))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub enum ConsensusTimeWireError {
    #[error("consensus-time-v1 wire length {0}, expected 16")]
    Length(usize),
    #[error("consensus-time-v1 wire has wrong magic")]
    Magic,
    #[error("unsupported consensus-time-v1 wire version {0}")]
    Version(u8),
    #[error("consensus-time-v1 reserved bytes are nonzero")]
    Reserved,
}

/// Versioned turn payload whose canonical block identity contains deterministic consensus time.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConsensusTimedTurnPayloadV1 {
    consensus_time: ConsensusTimeV1,
    signed_turn: Vec<u8>,
    receipt: Option<Vec<u8>>,
    witnessed_receipts: Vec<Vec<u8>>,
}

impl ConsensusTimedTurnPayloadV1 {
    pub fn new(consensus_unix_seconds: i64, signed_turn: Vec<u8>) -> Self {
        Self {
            consensus_time: ConsensusTimeV1::new(consensus_unix_seconds),
            signed_turn,
            receipt: None,
            witnessed_receipts: Vec::new(),
        }
    }

    pub fn with_artifacts(
        consensus_unix_seconds: i64,
        signed_turn: Vec<u8>,
        receipt: Option<Vec<u8>>,
        witnessed_receipts: Vec<Vec<u8>>,
    ) -> Self {
        Self {
            consensus_time: ConsensusTimeV1::new(consensus_unix_seconds),
            signed_turn,
            receipt,
            witnessed_receipts,
        }
    }

    pub const fn consensus_time(&self) -> ConsensusTimeV1 {
        self.consensus_time
    }

    pub fn signed_turn(&self) -> &[u8] {
        &self.signed_turn
    }

    pub fn receipt(&self) -> Option<&[u8]> {
        self.receipt.as_deref()
    }

    pub fn witnessed_receipts(&self) -> &[Vec<u8>] {
        &self.witnessed_receipts
    }

    fn validate_shape(&self) -> Result<(), BlockError> {
        let fits = |len: usize| u32::try_from(len).is_ok();
        if !fits(self.signed_turn.len())
            || self
                .receipt
                .as_ref()
                .is_some_and(|bytes| !fits(bytes.len()))
            || !fits(self.witnessed_receipts.len())
            || self
                .witnessed_receipts
                .iter()
                .any(|bytes| !fits(bytes.len()))
        {
            return Err(BlockError::ConsensusTimedTurnOversize);
        }
        Ok(())
    }
}

/// Full devnet artifact payload for a turn-bearing block.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TurnArtifactBundle {
    /// Node-encoded `dregg_sdk::SignedTurn` bytes.
    pub signed_turn: Vec<u8>,
    /// Node-encoded `dregg_turn::TurnReceipt`, when a node already has the
    /// committed receipt at block production time.
    pub receipt: Option<Vec<u8>>,
    /// Node-encoded `dregg_turn::WitnessedReceipt` artifacts for the
    /// receipt above. Multiple entries are expected for bilateral/gamma.2
    /// flows that produce per-cell witnessed receipts.
    pub witnessed_receipts: Vec<Vec<u8>>,
}

impl TurnArtifactBundle {
    pub fn new(signed_turn: Vec<u8>) -> Self {
        Self {
            signed_turn,
            receipt: None,
            witnessed_receipts: Vec::new(),
        }
    }

    /// Build the full artifact bundle for a *committed* turn.
    ///
    /// `signed_turn` is the node-encoded `dregg_sdk::SignedTurn`, `receipt` is
    /// the node-encoded committed `dregg_turn::TurnReceipt`, and
    /// `witnessed_receipts` carries one node-encoded
    /// `dregg_turn::WitnessedReceipt` artifact per cell that produced witness
    /// material at commit time. This is the production constructor that wires
    /// per-cell WitnessedReceipts into gossip so a peer's
    /// `materialize_blocklace_artifacts` receives real witnesses (rather than
    /// the empty `new()` vector that left the distributed witness path dead).
    pub fn with_committed(
        signed_turn: Vec<u8>,
        receipt: Option<Vec<u8>>,
        witnessed_receipts: Vec<Vec<u8>>,
    ) -> Self {
        Self {
            signed_turn,
            receipt,
            witnessed_receipts,
        }
    }
}

/// Membership actions for federation changes.
///
/// A `Propose` action initiates a membership change. An `Approve` action votes
/// on an existing proposal (referencing the block that contains the proposal).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum MembershipAction {
    /// Propose adding a node to the federation.
    ///
    /// ⚑ `ml_dsa_pubkey` IS LOAD-BEARING, NOT METADATA. `node_id` is the
    /// candidate's ed25519 STRAND key — the space `Constitution::participants`
    /// lives in — but every consensus-facing use of a member needs its
    /// POST-QUANTUM half too: the finality roster is keyed by the HYBRID id
    /// `H(ed25519 ‖ ml_dsa)` (`Block::creator`), the finalization-vote collector
    /// refuses a member with no ML-DSA key, and
    /// `blocklace_sync::project_committed_participants` DROPS an admitted member
    /// whose ML-DSA half is not in COMMITTED state — at which point
    /// `poll_finalized_blocks` FAILS CLOSED and the whole federation's finality
    /// HALTS.
    ///
    /// A Join that carried only `node_id` therefore could not succeed even if it
    /// were ratified: `ML-DSA.KeyGen` needs the seed, so no peer can DERIVE the
    /// candidate's PQ key, and nothing else on the wire carries it. Carrying it
    /// in the ratified payload is the only place every node sees the SAME bytes
    /// at the SAME point in the order, which is what "committed" has to mean for
    /// a value the tau leader schedule is a function of.
    ///
    /// It is covered by [`Block::canonical_bytes`] and therefore by the block's
    /// hybrid signature: a relay cannot substitute a different PQ key.
    Join {
        node_id: [u8; 32],
        ml_dsa_pubkey: crate::pq::MlDsaPublicKey,
    },
    /// Propose removing a node from the federation.
    Leave { node_id: [u8; 32] },
    /// Approve (vote yes on) an existing proposal contained in `proposal_block`.
    Approve { proposal_block: BlockId },
    /// Reject (vote no on) an existing proposal contained in `proposal_block`.
    Reject { proposal_block: BlockId },
}

/// A block in the blocklace.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Block {
    /// The creator's HYBRID identity: `H(ed25519_pubkey ‖ ml_dsa_pubkey)`
    /// ([`dregg_types::hybrid_id_commitment`]). This is the block's IDENTITY
    /// LABEL — the key the roster, tips, equivocation bookkeeping, cohort
    /// counting, votes and gossip `NodeId` all consume. It is NO LONGER the
    /// ed25519 verify key (that is carried separately in [`Self::ed25519`]); the
    /// id cryptographically COMMITS to BOTH the classical and the post-quantum
    /// public key, so an attacker who keeps the honest ed25519 key but presents
    /// their own ML-DSA key produces a DIFFERENT identity that the enroll+pin
    /// commitment check ([`dregg_types::verify_committed_ml_dsa`]) rejects.
    pub creator: [u8; 32],
    /// The creator's Ed25519 verify key (compressed point). Carried SEPARATELY
    /// from [`Self::creator`] (which is now the hybrid id) so it stays usable as
    /// the classical verify key. [`Self::verify_hybrid`] gates that this key,
    /// together with the enrolled ML-DSA key, commits to [`Self::creator`]
    /// BEFORE either signature is checked.
    #[serde(default)]
    pub ed25519: [u8; 32],
    /// Sequence number within this creator's virtual chain.
    pub seq: u64,
    /// The block's payload.
    pub payload: Payload,
    /// Hash pointers to predecessor blocks (what this block "sees").
    pub predecessors: Vec<BlockId>,
    /// Ed25519 signature over (creator, seq, payload_hash, predecessors).
    #[serde(with = "crate::serde_sig64")]
    pub signature: [u8; 64],
    /// The POST-QUANTUM half of the HYBRID block signature: an ML-DSA-65
    /// (FIPS 204) signature over the SAME canonical bytes as the ed25519 half
    /// (`id()`), produced by the key DERIVED from the creator's ed25519 seed
    /// ([`crate::pq::MlDsaSigningKey::from_seed`]). Empty (`vec![]`) is the
    /// PQ-absent sentinel — it fails [`Block::verify_hybrid`] closed. A hybrid
    /// block carries [`crate::pq::SIG_LEN`] (3309) bytes here.
    ///
    /// The live-consensus verifier PINS this against the creator's ENROLLED
    /// ML-DSA public key (the committee roster, [`Blocklace::enroll_pq`] /
    /// [`Blocklace::receive_block_pinned`]), NOT a key carried in the block — so
    /// a quantum adversary who forges the ed25519 half still cannot inject
    /// consensus blocks under another creator's identity. It is DELIBERATELY
    /// excluded from `id()` / [`PartialEq`] (ML-DSA hedged signing is
    /// randomized, so two signings of one block differ in these bytes yet are
    /// the same block).
    #[serde(default)]
    pub pq_signature: Vec<u8>,
}

impl PartialEq for Block {
    fn eq(&self, other: &Block) -> bool {
        self.creator == other.creator
            && self.seq == other.seq
            && self.payload == other.payload
            && self.predecessors == other.predecessors
            && self.signature == other.signature
    }
}

impl Eq for Block {}

/// Finality level for a block in the blocklace.
///
/// Blocks progress through finality levels as they accumulate acknowledgments:
/// Local -> Bilateral -> Attested -> Ordered
///
/// - Local: only the creator knows about this block.
/// - Bilateral: at least one other participant acknowledged it.
/// - Attested: a quorum (2f+1) acknowledged it.
/// - Ordered: the block is in the causal past of a super-ratified leader (total order assigned).
///
/// The ordering is monotone: once a block reaches a level, it never regresses.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum FinalityLevel {
    /// Block is known locally only (just created or received).
    Local,
    /// Block has been acknowledged by at least one other participant.
    Bilateral,
    /// Block has been attested by a quorum (2f+1 acknowledgments).
    Attested,
    /// Block has been included in a total order (consensus).
    Ordered,
}

/// Proof that a creator equivocated (produced conflicting blocks).
///
/// The pair of exhibits is the whole proof: two same-creator blocks,
/// incomparable under `≺`. Detection PINS this pair as the creator's
/// [`CreatorTips::Pair`] so it is carried into later blocks' closures, where
/// the per-closure exclusion predicate reads it ([`Blocklace::approved_by`],
/// Lean `Dregg2.Distributed.ExclusionByPast`). It never touches membership:
/// the former `equivocator_ed25519` accessor existed solely for the deleted
/// `auto_evict` membership mutation and is gone with it (exclusion-by-past
/// flag day 2026-08-08).
#[derive(Clone, Debug)]
pub struct EquivocationProof {
    /// The equivocator's HYBRID consensus id (`Block::creator`) — the label the
    /// lace's `equivocators` set, `tips` map and PQ roster are keyed by.
    pub creator: [u8; 32],
    pub block_a: Block,
    pub block_b: Block,
}

/// Metrics snapshot for observability.
#[derive(Clone, Debug)]
pub struct BlocklaceMetrics {
    /// Total number of blocks in the local view.
    pub block_count: usize,
    /// Number of detected equivocators.
    pub equivocator_count: usize,
    /// Finality lag: number of blocks between tip and last finalized.
    pub finality_lag: usize,
    /// Number of blocks that have been totally ordered.
    pub ordered_count: usize,
    /// Number of blocks that have been attested by quorum.
    pub attested_count: usize,
    /// Number of distinct block creators.
    pub creator_count: usize,
}

/// Flag-day configuration for consensus-time-v1 deterministic causal replay time.
///
/// The forward bound is a protocol constant; the sole deployment coordinate is the genesis time
/// which the signed predecessorless v1 block must reproduce exactly. CTM1 does **not** claim fair
/// wall-clock consensus; a producer can repeatedly select the causal maximum.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ConsensusTimePolicyV1 {
    genesis_unix_seconds: i64,
}

impl ConsensusTimePolicyV1 {
    pub const fn new(genesis_unix_seconds: i64) -> Self {
        Self {
            genesis_unix_seconds,
        }
    }

    pub const fn genesis_unix_seconds(self) -> i64 {
        self.genesis_unix_seconds
    }
}

/// State of ordering for blocks reaching consensus.
#[derive(Clone, Debug, Default)]
pub struct OrderingState {
    /// Blocks that have reached bilateral acknowledgment.
    pub bilateral: HashSet<BlockId>,
    /// Blocks that have been ordered (total order assigned).
    pub ordered: Vec<BlockId>,
    /// Blocks that have been attested by quorum.
    pub attested: HashSet<BlockId>,
}

// ─── Errors ──────────────────────────────────────────────────────────────────

/// Errors when receiving or merging blocks.
#[derive(Debug, thiserror::Error)]
pub enum BlockError {
    #[error("invalid signature on block from creator {creator:?} seq {seq}")]
    InvalidSignature { creator: [u8; 32], seq: u64 },

    #[error("missing predecessor {missing:?} for block from creator {creator:?} seq {seq}")]
    MissingPredecessor {
        creator: [u8; 32],
        seq: u64,
        missing: BlockId,
    },

    #[error("equivocation detected from creator {creator:?} at seq {seq}")]
    Equivocation {
        creator: [u8; 32],
        seq: u64,
        proof: EquivocationProof,
    },

    #[error("block from creator {creator:?} seq {seq} carries no post-quantum signature half")]
    UnsignedPq { creator: [u8; 32], seq: u64 },

    #[error(
        "invalid ML-DSA post-quantum signature on block from creator {creator:?} seq {seq} \
         (not signed by the creator's ENROLLED key)"
    )]
    BadPqSignature { creator: [u8; 32], seq: u64 },

    #[error(
        "no ML-DSA key enrolled for creator {creator:?} (block seq {seq} rejected fail-closed)"
    )]
    UnenrolledCreator { creator: [u8; 32], seq: u64 },

    #[error("consensus-time-v1 policy is not enabled")]
    ConsensusTimePolicyMissing,

    #[error("legacy timestamp-less turn payload refused after consensus-time-v1 cutover")]
    LegacyTurnAfterConsensusTimeCutover,

    #[error("consensus-time-v1 turn payload contains an oversized length/count")]
    ConsensusTimedTurnOversize,

    #[error("consensus-time-v1 genesis timestamp {actual} differs from anchor {expected}")]
    ConsensusGenesisTimeMismatch { expected: i64, actual: i64 },

    #[error("consensus timestamp {actual} regresses below predecessor frontier {minimum}")]
    ConsensusTimeRegression { minimum: i64, actual: i64 },

    #[error("consensus timestamp {actual} exceeds causal forward bound {maximum}")]
    ConsensusTimeForwardBound { maximum: i64, actual: i64 },

    #[error("consensus-time-v1 causal bound overflow")]
    ConsensusTimeBoundOverflow,

    #[error("consensus-time-v1 policy is already configured with another genesis anchor")]
    ConsensusTimePolicyReplacement,

    #[error("consensus-time-v1 flag day must be enabled before the first block")]
    ConsensusTimeFlagDayRequiresEmptyLace,

    #[error("consensus-time-v1 frontier missing for predecessor {predecessor:?}")]
    ConsensusTimeFrontierMissing { predecessor: BlockId },

    #[error("cannot rebuild consensus-time-v1 over a causally incomplete blocklace")]
    ConsensusTimeRestoreNotCausallyClosed,
}

/// Errors during delta-merge.
#[derive(Debug, thiserror::Error)]
pub enum MergeError {
    #[error("delta is not causally closed: missing {missing:?}")]
    NotCausallyClosed { missing: BlockId },

    #[error("block error during merge: {0}")]
    Block(#[from] BlockError),
}

// ─── Block Operations ────────────────────────────────────────────────────────

impl Block {
    /// Compute the content that gets signed: (creator, seq, payload_hash, predecessors).
    fn signing_content(
        creator: &[u8; 32],
        seq: u64,
        payload: &Payload,
        predecessors: &[BlockId],
    ) -> Vec<u8> {
        // Hash the payload to keep the signed content compact.
        let payload_hash = blake3::hash(&Self::payload_bytes(payload));
        Self::signing_content_from_payload_hash(creator, seq, payload_hash.as_bytes(), predecessors)
    }

    /// The signing content reconstructed from an already-computed payload
    /// hash. This is what makes a compact equivocation-evidence header
    /// ([`crate::evidence::EvidenceHeader`]) verifiable WITHOUT the payload
    /// (and without the lace): the header carries `(seq, payload_hash,
    /// predecessors, signature)` and any verifier rebuilds the exact signed
    /// bytes from it. Must stay byte-identical to [`Self::signing_content`].
    pub(crate) fn signing_content_from_payload_hash(
        creator: &[u8; 32],
        seq: u64,
        payload_hash: &[u8; 32],
        predecessors: &[BlockId],
    ) -> Vec<u8> {
        let mut buf = Vec::with_capacity(18 + 32 + 8 + 32 + predecessors.len() * 32);
        buf.extend_from_slice(b"dregg-blocklace-v1");
        buf.extend_from_slice(creator);
        buf.extend_from_slice(&seq.to_le_bytes());
        buf.extend_from_slice(payload_hash);
        for pred in predecessors {
            buf.extend_from_slice(&pred.0);
        }
        buf
    }

    /// Serialize a payload into bytes for hashing (deterministic).
    pub(crate) fn payload_bytes(payload: &Payload) -> Vec<u8> {
        let mut buf = Vec::new();
        match payload {
            Payload::Turn(data) => {
                buf.push(0x01);
                buf.extend_from_slice(&(data.len() as u32).to_le_bytes());
                buf.extend_from_slice(data);
            }
            Payload::TurnBundle(bundle) => {
                buf.push(0x06);
                buf.extend_from_slice(&(bundle.signed_turn.len() as u32).to_le_bytes());
                buf.extend_from_slice(&bundle.signed_turn);
                match &bundle.receipt {
                    Some(receipt) => {
                        buf.push(0x01);
                        buf.extend_from_slice(&(receipt.len() as u32).to_le_bytes());
                        buf.extend_from_slice(receipt);
                    }
                    None => buf.push(0x00),
                }
                buf.extend_from_slice(&(bundle.witnessed_receipts.len() as u32).to_le_bytes());
                for witnessed in &bundle.witnessed_receipts {
                    buf.extend_from_slice(&(witnessed.len() as u32).to_le_bytes());
                    buf.extend_from_slice(witnessed);
                }
            }
            Payload::ConsensusTimedTurnV1(bundle) => {
                // A fresh discriminant and fixed-width CTM1 header prevent legacy payload bytes
                // from silently acquiring consensus-time semantics at the flag day.
                buf.push(0x07);
                buf.extend_from_slice(&bundle.consensus_time.encode());
                buf.extend_from_slice(&(bundle.signed_turn.len() as u32).to_le_bytes());
                buf.extend_from_slice(&bundle.signed_turn);
                match &bundle.receipt {
                    Some(receipt) => {
                        buf.push(0x01);
                        buf.extend_from_slice(&(receipt.len() as u32).to_le_bytes());
                        buf.extend_from_slice(receipt);
                    }
                    None => buf.push(0x00),
                }
                buf.extend_from_slice(&(bundle.witnessed_receipts.len() as u32).to_le_bytes());
                for witnessed in &bundle.witnessed_receipts {
                    buf.extend_from_slice(&(witnessed.len() as u32).to_le_bytes());
                    buf.extend_from_slice(witnessed);
                }
            }
            Payload::Ack => {
                buf.push(0x02);
            }
            Payload::Checkpoint { root, height } => {
                buf.push(0x03);
                buf.extend_from_slice(root);
                buf.extend_from_slice(&height.to_le_bytes());
            }
            Payload::MembershipVote { action } => {
                buf.push(0x04);
                match action {
                    MembershipAction::Join {
                        node_id,
                        ml_dsa_pubkey,
                    } => {
                        buf.push(0x01);
                        buf.extend_from_slice(node_id);
                        // The candidate's PQ half is INSIDE the signed preimage.
                        // Length-prefixed even though `PK_LEN` is fixed, so the
                        // encoding stays unambiguous if the suite ever rotates.
                        buf.extend_from_slice(&(ml_dsa_pubkey.0.len() as u32).to_le_bytes());
                        buf.extend_from_slice(&ml_dsa_pubkey.0);
                    }
                    MembershipAction::Leave { node_id } => {
                        buf.push(0x02);
                        buf.extend_from_slice(node_id);
                    }
                    MembershipAction::Approve { proposal_block } => {
                        buf.push(0x03);
                        buf.extend_from_slice(&proposal_block.0);
                    }
                    MembershipAction::Reject { proposal_block } => {
                        buf.push(0x04);
                        buf.extend_from_slice(&proposal_block.0);
                    }
                }
            }
            Payload::Data(data) => {
                buf.push(0x05);
                buf.extend_from_slice(&(data.len() as u32).to_le_bytes());
                buf.extend_from_slice(data);
            }
        }
        buf
    }

    /// Compute this block's ID (blake3 hash of signed content + signature).
    pub fn id(&self) -> BlockId {
        let mut buf =
            Self::signing_content(&self.creator, self.seq, &self.payload, &self.predecessors);
        buf.extend_from_slice(&self.signature);
        BlockId(*blake3::hash(&buf).as_bytes())
    }

    /// Verify this block's Ed25519 signature against the CARRIED ed25519 key
    /// ([`Self::ed25519`]), over the signing content (which commits to the hybrid
    /// [`Self::creator`] id). The ed25519 key is no longer the identity label, so
    /// verification parses [`Self::ed25519`], not `creator`.
    pub fn verify_signature(&self) -> Result<(), BlockError> {
        let content =
            Self::signing_content(&self.creator, self.seq, &self.payload, &self.predecessors);
        let verifying_key =
            VerifyingKey::from_bytes(&self.ed25519).map_err(|_| BlockError::InvalidSignature {
                creator: self.creator,
                seq: self.seq,
            })?;
        let signature = ed25519_dalek::Signature::from_bytes(&self.signature);
        verifying_key
            .verify_strict(&content, &signature)
            .map_err(|_| BlockError::InvalidSignature {
                creator: self.creator,
                seq: self.seq,
            })
    }

    /// Serialize the block to bytes for wire transmission.
    ///
    /// Uses postcard's compact binary format. The result is deterministic
    /// for a given block (same bytes every time).
    pub fn to_bytes(&self) -> Vec<u8> {
        postcard::to_stdvec(self).expect("block serialization should not fail")
    }

    /// Deserialize a block from bytes.
    ///
    /// Returns `None` if the bytes are malformed.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        postcard::from_bytes(bytes).ok()
    }

    /// Create and HYBRID-sign a new block (ed25519 ∧ ML-DSA-65) with an identity
    /// whose ML-DSA key was derived ONCE, at the signer's construction.
    ///
    /// The ed25519 half signs the compact `signing_content`; the post-quantum
    /// half signs the canonical `id()` (which already commits to the ed25519
    /// signature) with the signer's held ML-DSA key — derived from the SAME
    /// ed25519 seed, so the creator never manages a separate PQ key and the
    /// enrolled PQ public key is a deterministic function of the ed25519
    /// identity. On a transient OS-entropy failure during hedged ML-DSA signing
    /// the PQ half is left empty — such a block fails [`Block::verify_hybrid`]
    /// closed rather than passing half-signed.
    ///
    /// **This is the authoring path.** [`Block::new`] is the same code with a
    /// one-shot signer in front of it; every byte of the result is identical,
    /// which is what `signer_path_is_byte_identical_to_the_one_shot` pins.
    pub fn new_signed_by(
        signer: &crate::signer::HybridBlockSigner,
        seq: u64,
        payload: Payload,
        predecessors: Vec<BlockId>,
    ) -> Self {
        let creator = signer.creator();
        // The ed25519 half signs the content, which commits to the hybrid id.
        let content = Self::signing_content(&creator, seq, &payload, &predecessors);
        let signature = signer.classical().sign(&content);
        let mut block = Block {
            creator,
            ed25519: signer.ed25519(),
            seq,
            payload,
            predecessors,
            signature: signature.to_bytes(),
            pq_signature: Vec::new(),
        };
        // POST-QUANTUM half: sign the SAME canonical bytes the verifier pins
        // (`id()`) with the from-seed ML-DSA key.
        let id = block.id();
        block.pq_signature = signer.sign_pq(&id.0).unwrap_or_default();
        block
    }

    /// Create and HYBRID-sign a new block from a BARE ed25519 signing key.
    ///
    /// ⚠ A ONE-SHOT: it builds a [`crate::signer::HybridBlockSigner`], uses it
    /// once and drops it, so it pays a **full ML-DSA-65 keygen per block**. Any
    /// caller that authors more than one block for one identity — every node
    /// does — should hold a signer and call [`Block::new_signed_by`], which is
    /// byte-identical. [`Blocklace`] already does.
    pub fn new(
        signing_key: &SigningKey,
        seq: u64,
        payload: Payload,
        predecessors: Vec<BlockId>,
    ) -> Self {
        Self::new_signed_by(
            &crate::signer::HybridBlockSigner::new(signing_key.clone()),
            seq,
            payload,
            predecessors,
        )
    }

    /// The HYBRID identity for a creator whose ed25519 signing key is
    /// `signing_key`: `H(ed25519_pubkey ‖ from-seed ml_dsa_pubkey)`. This is the
    /// value [`Block::new`] stamps as `creator`, the key the roster / tips /
    /// votes / gossip `NodeId` are all keyed by. Equal to
    /// [`Block::hybrid_id_from_parts`] on the two derived public keys.
    ///
    /// ⚠ A ONE-SHOT — it pays a full ML-DSA-65 keygen. A holder of a
    /// [`crate::signer::HybridBlockSigner`] reads the same value off
    /// [`crate::signer::HybridBlockSigner::creator`] for free.
    pub fn hybrid_id(signing_key: &SigningKey) -> [u8; 32] {
        crate::signer::HybridBlockSigner::new(signing_key.clone()).creator()
    }

    /// The HYBRID identity from an ed25519 verify key and an ML-DSA public key.
    /// Used at committee-learning boundaries (enrollment / participant sets)
    /// where both public halves are known but no secret seed is: the same value
    /// [`Block::new`] produces as `creator`.
    pub fn hybrid_id_from_parts(
        ed25519: &[u8; 32],
        ml_dsa: &crate::pq::MlDsaPublicKey,
    ) -> [u8; 32] {
        dregg_types::hybrid_id_commitment(ed25519, &ml_dsa.0)
    }

    /// The enrollable ML-DSA-65 public key for a creator whose ed25519 signing
    /// key is `signing_key` — the roster entry a verifier PINS this creator's
    /// consensus blocks against ([`Blocklace::enroll_pq`]). Equal to
    /// [`crate::pq::public_from_ed25519_seed`] on the key's seed.
    /// ⚠ A ONE-SHOT — it pays a full ML-DSA-65 keygen. A holder of a
    /// [`crate::signer::HybridBlockSigner`] reads the same key off
    /// [`crate::signer::HybridBlockSigner::pq_public_key`] for free, and a lace
    /// reads its own off [`Blocklace::self_pq_public_key`].
    ///
    /// Routed through the signer rather than calling
    /// `crate::pq::public_from_ed25519_seed` directly, so this crate has exactly ONE
    /// place a block-creator ML-DSA key is derived. When it had two, a mutation of
    /// one was only half-caught by the tests.
    pub fn pq_public_key(signing_key: &SigningKey) -> crate::pq::MlDsaPublicKey {
        crate::signer::HybridBlockSigner::new(signing_key.clone())
            .pq_public_key()
            .clone()
    }

    /// Whether this block carries BOTH halves of a (syntactically) non-zero
    /// hybrid signature. A zeroed ed25519 signature or an empty ML-DSA half is
    /// the unsigned sentinel; neither can be a valid hybrid signature.
    pub fn is_signed_hybrid(&self) -> bool {
        self.signature != [0u8; 64] && !self.pq_signature.is_empty()
    }

    /// Verify this block's HYBRID signature: Ed25519 against its self-carried
    /// `creator` pubkey AND ML-DSA-65 against the creator's ENROLLED PQ public
    /// key `enrolled_pq` (the committee roster, NOT a key carried in the block).
    ///
    /// Returns `Ok(())` iff BOTH halves verify. Rejects the missing-PQ sentinel
    /// ([`BlockError::UnsignedPq`]), a forged/mismatched ed25519 half
    /// ([`BlockError::InvalidSignature`]), and a PQ half that was not signed by
    /// the enrolled key ([`BlockError::BadPqSignature`]) — the case a quantum
    /// adversary who forges the ed25519 half, or who signs the PQ half under
    /// their OWN fresh ML-DSA key, cannot escape.
    pub fn verify_hybrid(&self, enrolled_pq: &crate::pq::MlDsaPublicKey) -> Result<(), BlockError> {
        // (0) COMMITMENT GATE (out-of-band → cryptographic): the block's `creator`
        // id MUST commit to BOTH the carried ed25519 key AND the enrolled ML-DSA
        // key. An attacker who keeps the honest ed25519 key but signs / presents
        // their OWN ML-DSA key gets an id that does not recompute to `creator`, so
        // this rejects BEFORE either signature is examined. This is what upgrades
        // the roster PIN from a trusted out-of-band binding to a cryptographic one:
        // the id IS the enrollment.
        if !dregg_types::verify_committed_ml_dsa(&self.creator, &self.ed25519, &enrolled_pq.0) {
            return Err(BlockError::BadPqSignature {
                creator: self.creator,
                seq: self.seq,
            });
        }
        // (a) Classical half: real Ed25519 verification against the carried key.
        self.verify_signature()?;
        // (b) Post-quantum half MUST be present (fail-closed, never treated as a
        // valid ed25519-only block).
        if self.pq_signature.is_empty() {
            return Err(BlockError::UnsignedPq {
                creator: self.creator,
                seq: self.seq,
            });
        }
        // (c) ML-DSA-65 PINNED to the ENROLLED roster key over the same `id()`.
        if !enrolled_pq.verify(&self.id().0, &self.pq_signature) {
            return Err(BlockError::BadPqSignature {
                creator: self.creator,
                seq: self.seq,
            });
        }
        Ok(())
    }
}

// ─── Finality Tracker ────────────────────────────────────────────────────────

/// Tracks finality progression for blocks in the blocklace.
///
/// As blocks accumulate acknowledgments from other participants, they progress
/// through finality levels: Local -> Bilateral -> Ordered -> Attested.
#[derive(Clone)]
pub struct FinalityTracker {
    /// How many acks each block has received (counted by unique creators).
    ack_counts: HashMap<BlockId, HashSet<[u8; 32]>>,
    /// Ordering state.
    pub ordering: OrderingState,
    /// Quorum threshold (typically 2f+1 where f = max Byzantine faults).
    quorum_threshold: usize,
}

impl FinalityTracker {
    /// Create a new finality tracker with the given quorum threshold.
    pub fn new(quorum_threshold: usize) -> Self {
        FinalityTracker {
            ack_counts: HashMap::new(),
            ordering: OrderingState::default(),
            quorum_threshold,
        }
    }

    /// Record that a block was acknowledged by a given creator.
    /// Returns the new finality level for the block.
    ///
    /// The returned level is monotone: once a block reaches Attested, subsequent
    /// acks still return Attested (it never regresses to Bilateral).
    pub fn record_ack(&mut self, block_id: BlockId, acker: [u8; 32]) -> FinalityLevel {
        let ackers = self.ack_counts.entry(block_id).or_default();
        ackers.insert(acker);

        if ackers.len() >= self.quorum_threshold {
            self.ordering.attested.insert(block_id);
            FinalityLevel::Attested
        } else {
            // At least one acker is present (we just inserted), so this is Bilateral.
            self.ordering.bilateral.insert(block_id);
            FinalityLevel::Bilateral
        }
    }

    /// Get the finality level for a block.
    ///
    /// Returns the highest level reached. Finality is monotone:
    /// Local < Bilateral < Attested < Ordered.
    pub fn finality_of(&self, block_id: &BlockId) -> FinalityLevel {
        if self.ordering.ordered.contains(block_id) {
            FinalityLevel::Ordered
        } else if self.ordering.attested.contains(block_id) {
            FinalityLevel::Attested
        } else if self.ordering.bilateral.contains(block_id) {
            FinalityLevel::Bilateral
        } else {
            FinalityLevel::Local
        }
    }

    /// Mark a block as ordered (included in total order by consensus).
    pub fn mark_ordered(&mut self, block_id: BlockId) {
        self.ordering.ordered.push(block_id);
    }

    /// Get the total order sequence so far.
    pub fn ordered_sequence(&self) -> &[BlockId] {
        &self.ordering.ordered
    }
}

// ─── Blocklace Container ─────────────────────────────────────────────────────

/// The tips a single creator contributes to the frontier — at most TWO, by type
/// (Cordial Miners Alg. 1:5, "at most two tips per miner").
///
/// `One` is the honest steady state: a correct creator's blocks form a single
/// virtual chain, so it has exactly one maximal block. `Pair` is pinned the
/// moment an equivocation is DETECTED: the two halves of the detected
/// incomparable pair. Keeping BOTH halves as tips is the CM two-tips rule read
/// in the direction that matters — it is a *floor on the evidence*, not just a
/// cap on the flood. The next block we author points at both halves, carrying
/// the equivocating pair into that block's causal closure, where every
/// anchor-relative exclusion predicate (`approved_by`, `ordering.rs::approves`,
/// Lean `Dregg2.Distributed.ExclusionByPast` / `hasEquivInPast`) can actually
/// see it. The previous shape — one tip per creator, dropped to zero on
/// detection — retained the second fork block as an *unreferenced* block,
/// outside every causal past, so `node(b) ∉ byz(⌊b⌋)` (blocklace paper
/// arXiv:2402.08068 §4.3) had nothing to evaluate and exclusion had to become a
/// node-local membership mutation instead (the F-CO-1 fork reopened).
///
/// The flood bound lives in the same place: an equivocator producing `k`
/// mutually-incomparable blocks pins exactly the FIRST detected pair (the entry
/// is frozen once the creator is flagged — see `insert_checked`), so our
/// pointer contribution per creator is ≤ 2 regardless of `k`. CM's bound,
/// enforced structurally by this type rather than by a runtime check.
///
/// WHICH pair gets pinned depends on local detection order and may differ
/// between honest nodes — that is fine: the exclusion predicate is existential
/// (`∃` an incomparable pair in the anchor's closure), so ANY carried pair
/// yields the same per-anchor verdict, and the verdict is a function of the
/// anchor's closure, never of which pair a particular node happened to carry.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CreatorTips {
    /// The creator's single maximal block (honest virtual chain).
    One(BlockId),
    /// A detected equivocating pair, pinned as evidence to be carried into the
    /// closure of the next locally-authored block. Frozen while the creator is
    /// flagged; cleared once a locally-authored block points at both halves
    /// (the evidence path is then welded through our own chain).
    Pair(BlockId, BlockId),
}

impl CreatorTips {
    /// Construct a pinned pair in CANONICAL (sorted-by-id) order, so the tips
    /// entry — and everything derived from it (frontier announcements, the
    /// authored predecessor list) — is byte-identical across nodes regardless
    /// of which fork half arrived first. Which PAIR gets pinned may still
    /// differ (see the type docs); its internal order never does.
    pub fn pair(a: BlockId, b: BlockId) -> Self {
        if a.0 <= b.0 {
            CreatorTips::Pair(a, b)
        } else {
            CreatorTips::Pair(b, a)
        }
    }

    /// Iterate the (one or two) tip ids.
    pub fn iter(&self) -> impl Iterator<Item = BlockId> + '_ {
        match *self {
            CreatorTips::One(a) => [Some(a), None],
            CreatorTips::Pair(a, b) => [Some(a), Some(b)],
        }
        .into_iter()
        .flatten()
    }

    /// The primary tip: the creator's chain head for `One`; for a pinned
    /// `Pair` there is no meaningful "latest" (the halves are incomparable),
    /// so the first half is returned. Callers that need "the honest chain
    /// head" should treat a `Pair` creator as an equivocator instead.
    pub fn primary(&self) -> BlockId {
        match *self {
            CreatorTips::One(a) | CreatorTips::Pair(a, _) => a,
        }
    }
}

/// The blocklace: a local view of the global DAG.
///
/// Each node maintains its own Blocklace instance. The blocklace grows monotonically
/// via CRDT union-merge: receiving blocks from peers can only add to the local view,
/// never remove.
///
/// `Clone` is a cheap structural copy (the `self_key` is a 32-byte Ed25519 key) used by
/// the node's `poll_finalized_blocks` to SNAPSHOT the lace and release the read lock
/// before the O(history) verified-Lean tau-order FFI, so block production is never
/// starved (the live-federation round-production halt).
#[derive(Clone)]
pub struct Blocklace {
    /// All known blocks.
    pub(crate) blocks: HashMap<BlockId, Block>,
    /// Per-creator tip tracking: the creator's maximal block, or — for a
    /// detected equivocator — the pinned evidence pair (see [`CreatorTips`]).
    tips: HashMap<[u8; 32], CreatorTips>,
    /// Detected equivocators.
    equivocators: HashSet<[u8; 32]>,
    /// Our own HYBRID signing identity: the ed25519 key AND the ML-DSA-65 key its
    /// seed derives, derived ONCE here rather than per authored block.
    ///
    /// This field used to be a bare `self_key: SigningKey`, and authoring one block
    /// cost TWO full ML-DSA-65 keygens for this one unchanging identity — one in
    /// `Block::new(&self.self_key, ..)` and one in `self_creator()` →
    /// `Block::hybrid_id(&self.self_key)` to key the tips map. A node authored a
    /// block per round and paid both every time.
    ///
    /// The lace OWNS the seed for its whole life, so the derived key belongs here.
    /// `Clone` stays cheap (the PQ halves are behind `Arc`s), which the node's
    /// `poll_finalized_blocks` snapshot depends on.
    signer: crate::signer::HybridBlockSigner,
    /// Our own sequence counter.
    self_seq: u64,
    /// Finality tracking.
    pub finality: FinalityTracker,
    /// The ENROLLED ML-DSA-65 committee roster: `creator (ed25519 pubkey) ->
    /// enrolled ML-DSA public key`. The live-consensus reception
    /// [`Blocklace::receive_block_pinned`] PINS a block's post-quantum half to
    /// the enrolled key for its creator; a block whose creator is absent from
    /// the roster is rejected fail-closed ([`BlockError::UnenrolledCreator`]).
    /// Populated out-of-band from the trusted committee roster (genesis /
    /// membership), via [`Blocklace::enroll_pq`] — the block never carries its
    /// own PQ key.
    pq_roster: HashMap<[u8; 32], crate::pq::MlDsaPublicKey>,
    /// `Some` after the deterministic-time flag day. Legacy turn payloads then fail closed at
    /// admission; non-turn DAG traffic remains compatible.
    consensus_time_v1: Option<ConsensusTimePolicyV1>,
    /// Derived authenticated-time frontier for each post-flag-day block.
    ///
    /// Admission reads only the immediate predecessors' cached frontiers, so causal-time
    /// validation is O(predecessor count) instead of repeatedly walking all ancestors.
    consensus_time_frontier_v1: HashMap<BlockId, i64>,
}

impl Blocklace {
    /// Create a new blocklace with the given signing key and quorum threshold.
    ///
    /// Derives this identity's ML-DSA-65 half ONCE, here — every block the lace
    /// authors afterwards, and every `self_creator()`, is keygen-free.
    pub fn new(self_key: SigningKey, quorum_threshold: usize) -> Self {
        Self::with_signer(
            crate::signer::HybridBlockSigner::new(self_key),
            quorum_threshold,
        )
    }

    /// Create a new blocklace from an ALREADY-DERIVED hybrid identity — for a
    /// caller (a node holding its own identity, a test committee) that already has
    /// a [`crate::signer::HybridBlockSigner`] and should not pay a second keygen to
    /// build a lace with it.
    pub fn with_signer(signer: crate::signer::HybridBlockSigner, quorum_threshold: usize) -> Self {
        Blocklace {
            blocks: HashMap::new(),
            tips: HashMap::new(),
            equivocators: HashSet::new(),
            signer,
            self_seq: 0,
            finality: FinalityTracker::new(quorum_threshold),
            pq_roster: HashMap::new(),
            consensus_time_v1: None,
            consensus_time_frontier_v1: HashMap::new(),
        }
    }

    /// Enroll a creator's ML-DSA-65 public key into the committee roster.
    ///
    /// After enrollment, [`Blocklace::receive_block_pinned`] PINS every block by
    /// `creator` to `pubkey`. The key comes from trusted out-of-band enrollment
    /// (genesis / membership committee roster); the block never carries its own
    /// PQ key. Re-enrolling replaces the key (committee rotation). The enrollable
    /// key is [`Block::pq_public_key`] on the creator's ed25519 signing key.
    pub fn enroll_pq(&mut self, creator: [u8; 32], pubkey: crate::pq::MlDsaPublicKey) {
        self.pq_roster.insert(creator, pubkey);
    }

    /// The enrolled ML-DSA committee roster (`creator -> enrolled PQ pubkey`).
    pub fn pq_roster(&self) -> &HashMap<[u8; 32], crate::pq::MlDsaPublicKey> {
        &self.pq_roster
    }

    /// Create a blocklace without finality tracking (quorum = 1, for testing).
    pub fn new_simple(self_key: SigningKey) -> Self {
        Self::new(self_key, 1)
    }

    /// Enable the deterministic consensus-time flag day for this lace.
    ///
    /// Repeating the identical policy is idempotent; replacing the genesis anchor is refused. The
    /// live node must persist/configure this coordinate from federation genesis before accepting
    /// post-cutover turn blocks.
    pub fn enable_consensus_time_v1(
        &mut self,
        policy: ConsensusTimePolicyV1,
    ) -> Result<(), BlockError> {
        match self.consensus_time_v1 {
            Some(existing) if existing == policy => Ok(()),
            Some(_) => Err(BlockError::ConsensusTimePolicyReplacement),
            None if !self.blocks.is_empty() => {
                Err(BlockError::ConsensusTimeFlagDayRequiresEmptyLace)
            }
            None => {
                self.consensus_time_v1 = Some(policy);
                Ok(())
            }
        }
    }

    /// Install consensus-time-v1 while restoring an authenticated pre-existing lace.
    ///
    /// Checkpoints intentionally persist signed blocks, not this derived frontier cache. Recovery
    /// therefore topologically replays the deterministic time rule over every authenticated block.
    /// The operation is atomic: a legacy turn, invalid claim, or broken causal graph leaves both
    /// the current policy and cache unchanged. This is also the explicit flag-day migration gate:
    /// old timestamp-less turn histories are refused rather than silently reinterpreted.
    pub fn restore_consensus_time_v1(
        &mut self,
        policy: ConsensusTimePolicyV1,
    ) -> Result<(), BlockError> {
        if self
            .consensus_time_v1
            .is_some_and(|existing| existing != policy)
        {
            return Err(BlockError::ConsensusTimePolicyReplacement);
        }

        let mut candidate = self.clone();
        candidate.consensus_time_v1 = Some(policy);
        candidate.consensus_time_frontier_v1.clear();

        let blocks: Vec<Block> = candidate.blocks.values().cloned().collect();
        let sorted = topological_sort(&blocks, &HashMap::new())
            .map_err(|_| BlockError::ConsensusTimeRestoreNotCausallyClosed)?;
        if sorted.len() != blocks.len() {
            return Err(BlockError::ConsensusTimeRestoreNotCausallyClosed);
        }

        for block in sorted {
            let frontier = candidate.validated_consensus_time_frontier_v1(&block)?;
            if let Some(frontier) = frontier {
                candidate
                    .consensus_time_frontier_v1
                    .insert(block.id(), frontier);
            }
        }

        self.consensus_time_v1 = candidate.consensus_time_v1;
        self.consensus_time_frontier_v1 = candidate.consensus_time_frontier_v1;
        Ok(())
    }

    pub const fn consensus_time_policy_v1(&self) -> Option<ConsensusTimePolicyV1> {
        self.consensus_time_v1
    }

    /// Our own HYBRID creator id (`H(ed25519 ‖ ml_dsa)`) — the same value
    /// [`Block::new`] stamps on the blocks we author, so `tips`, cohort counting
    /// and round planning key our own blocks consistently.
    ///
    /// A field read. It used to be `Block::hybrid_id(&self.self_key)`, i.e. a full
    /// ML-DSA-65 keygen, and `try_add_block_with_predecessors` calls it on every
    /// authored block.
    pub fn self_creator(&self) -> [u8; 32] {
        self.signer.creator()
    }

    /// Our own Ed25519 verify key (the CARRIED classical half). Distinct from
    /// [`Self::self_creator`], which is now the hybrid identity.
    pub fn self_ed25519(&self) -> [u8; 32] {
        self.signer.ed25519()
    }

    /// Our own ENROLLABLE ML-DSA-65 public key — the roster entry peers PIN this
    /// node's blocks against. Free; no derivation.
    pub fn self_pq_public_key(&self) -> &crate::pq::MlDsaPublicKey {
        self.signer.pq_public_key()
    }

    /// Our own HYBRID signing identity, for a caller that needs to author through
    /// it directly (or to build a second lace without re-deriving).
    pub fn signer(&self) -> &crate::signer::HybridBlockSigner {
        &self.signer
    }

    /// Number of blocks in the local view.
    pub fn len(&self) -> usize {
        self.blocks.len()
    }

    /// Whether the blocklace is empty.
    pub fn is_empty(&self) -> bool {
        self.blocks.is_empty()
    }

    /// Get a block by ID.
    pub fn get(&self, id: &BlockId) -> Option<&Block> {
        self.blocks.get(id)
    }

    /// Check if a block is known.
    pub fn contains(&self, id: &BlockId) -> bool {
        self.blocks.contains_key(id)
    }

    /// Get detected equivocators.
    pub fn equivocators(&self) -> &HashSet<[u8; 32]> {
        &self.equivocators
    }

    /// Get metrics about the current blocklace state.
    pub fn metrics(&self) -> BlocklaceMetrics {
        let last_ordered = self.finality.ordering.ordered.last().copied();
        let finality_lag = if last_ordered.is_some() {
            self.blocks.len() - self.finality.ordering.ordered.len()
        } else {
            self.blocks.len()
        };

        BlocklaceMetrics {
            block_count: self.blocks.len(),
            equivocator_count: self.equivocators.len(),
            finality_lag,
            ordered_count: self.finality.ordering.ordered.len(),
            attested_count: self.finality.ordering.attested.len(),
            creator_count: self.tips.len(),
        }
    }

    /// Get current tips: per creator, the maximal block — or, for a detected
    /// equivocator, the pinned evidence pair (see [`CreatorTips`]).
    pub fn tips(&self) -> &HashMap<[u8; 32], CreatorTips> {
        &self.tips
    }

    /// All tip block ids, flattened across creators (≤ 2 per creator by type).
    /// This is the pointer set a locally-authored block links: the honest
    /// frontier PLUS both halves of every pinned equivocating pair — the CM
    /// Alg. 1:5 evidence floor.
    pub fn tip_ids(&self) -> Vec<BlockId> {
        self.tips.values().flat_map(CreatorTips::iter).collect()
    }

    /// The primary tip for one creator (its chain head; for a flagged
    /// equivocator, the first pinned half — see [`CreatorTips::primary`]).
    pub fn creator_tip(&self, creator: &[u8; 32]) -> Option<BlockId> {
        self.tips.get(creator).map(CreatorTips::primary)
    }

    /// The pinned evidence pairs: every creator whose tips entry currently
    /// carries a detected incomparable pair not yet welded into a
    /// locally-authored block's closure. The round-driven producer links these
    /// so the pair reaches every later block's causal past.
    pub fn pinned_evidence_pairs(&self) -> impl Iterator<Item = ([u8; 32], BlockId, BlockId)> + '_ {
        self.tips.iter().filter_map(|(c, t)| match t {
            CreatorTips::Pair(a, b) => Some((*c, *a, *b)),
            CreatorTips::One(_) => None,
        })
    }

    /// Get a reference to the signing key.
    pub fn signing_key(&self) -> &SigningKey {
        self.signer.classical()
    }

    // ─── Block Creation ──────────────────────────────────────────────────

    /// Create a new block with the given payload.
    /// Predecessors = all current tips (what we currently know about).
    pub fn add_block(&mut self, payload: Payload) -> Block {
        self.try_add_block(payload)
            .expect("generic local block violates consensus-time-v1; use the fallible constructor")
    }

    /// Fallible local block creation, including deterministic-time admission when enabled.
    ///
    /// Failure is atomic: sequence, tips, frontier index, and block map remain unchanged.
    pub fn try_add_block(&mut self, payload: Payload) -> Result<Block, BlockError> {
        let predecessors: Vec<BlockId> = self.tip_ids();
        self.try_add_block_with_predecessors(payload, predecessors)
    }

    /// Fallible local block creation over an exact predecessor cohort.
    ///
    /// This is the atomic counterpart of [`Self::add_block_with_predecessors`] for protocol paths
    /// that must surface a consensus-time or causal-frontier refusal instead of panicking.
    pub fn try_add_block_with_predecessors(
        &mut self,
        payload: Payload,
        predecessors: Vec<BlockId>,
    ) -> Result<Block, BlockError> {
        let next_seq = self
            .self_seq
            .checked_add(1)
            .ok_or(BlockError::ConsensusTimeBoundOverflow)?;
        // Authored through the HELD identity: no ML-DSA keygen. Byte-identical to
        // `Block::new(self.signing_key(), ..)` — the one-shot builds this same
        // signer and calls this same `new_signed_by`.
        let block = Block::new_signed_by(&self.signer, next_seq, payload, predecessors);
        let frontier = self.validated_consensus_time_frontier_v1(&block)?;
        self.self_seq = next_seq;
        let id = block.id();
        self.blocks.insert(id, block.clone());
        if let Some(frontier) = frontier {
            self.consensus_time_frontier_v1.insert(id, frontier);
        }
        self.tips.insert(self.self_creator(), CreatorTips::One(id));
        // EVIDENCE WELD: any pinned equivocating pair whose BOTH halves this
        // block just pointed at is now in our own tip's causal closure — every
        // future block we author observes it transitively through our chain.
        // Drop the pinned entry so the pair is carried ONCE (the CM two-tips
        // floor is transient: carry the pair forward, then repel — no further
        // direct acks of the equivocator; `insert_checked` never re-populates a
        // flagged creator's entry).
        self.tips.retain(|_, t| match t {
            CreatorTips::Pair(a, b) => {
                !(block.predecessors.contains(a) && block.predecessors.contains(b))
            }
            CreatorTips::One(_) => true,
        });
        Ok(block)
    }

    /// Create a new block with explicit predecessors (for advanced usage).
    pub fn add_block_with_predecessors(
        &mut self,
        payload: Payload,
        predecessors: Vec<BlockId>,
    ) -> Block {
        self.try_add_block_with_predecessors(payload, predecessors)
            .expect("local block violates consensus-time-v1")
    }

    /// Undo the most recent LOCALLY-AUTHORED block after its durable persist
    /// FAILED, BEFORE it is broadcast — the exact inverse of the four mutations
    /// [`Self::try_add_block_with_predecessors`] makes (`self_seq`, `blocks`,
    /// `consensus_time_frontier_v1`, our `tips` entry).
    ///
    /// The self strand's next sequence is rebuilt on boot from PERSISTED blocks
    /// ONLY. So an authored-but-unpersisted tip left live here would, after a
    /// crash, be re-authored at the same `(creator, seq)` with different content
    /// — a slashable **self-equivocation** (node durability finding F2). Rolling
    /// the block back keeps the live lace equal to durable state, so the caller
    /// can safely refuse to broadcast it.
    ///
    /// MUST be called while STILL holding the write access that authored the
    /// block, with `block_id` still our current self-tip (no successor authored
    /// on top — persist inside the same lock guarantees this). Returns `true`
    /// when a local-authored self-tip was rolled back; `false` (a no-op) when
    /// `block_id` is not our current self-authored tip — never rolls back a peer
    /// block or a superseded one.
    pub fn rollback_local_authored(&mut self, block_id: BlockId) -> bool {
        let self_creator = self.self_creator();
        // Only ever roll back OUR OWN current tip. A `Pair` entry for self means
        // we are a flagged self-equivocator — never roll back through that.
        if self.tips.get(&self_creator) != Some(&CreatorTips::One(block_id)) {
            return false;
        }
        let seq = match self.blocks.get(&block_id) {
            Some(block) if block.creator == self_creator => block.seq,
            _ => return false,
        };
        // Restore our tip to the prior self-authored block at seq-1, if any (a
        // rolled-back genesis block has no prior self tip → withdraw the entry).
        let prev_self_tip = self
            .blocks
            .values()
            .find(|b| b.creator == self_creator && b.seq + 1 == seq)
            .map(Block::id);
        match prev_self_tip {
            Some(prev) => {
                self.tips.insert(self_creator, CreatorTips::One(prev));
            }
            None => {
                self.tips.remove(&self_creator);
            }
        }
        self.self_seq = seq.saturating_sub(1);
        self.blocks.remove(&block_id);
        self.consensus_time_frontier_v1.remove(&block_id);
        true
    }

    /// Produce a locally-authored consensus-timed turn through the strict v1 path.
    ///
    /// Unlike generic [`Self::add_block`], this returns an error before changing sequence, tips, or
    /// the block map when the claimed time violates genesis/causal bounds. The node flag-day cut
    /// should use this constructor exclusively for turn-bearing blocks.
    pub fn add_consensus_timed_turn_v1(
        &mut self,
        payload: ConsensusTimedTurnPayloadV1,
    ) -> Result<Block, BlockError> {
        let predecessors: Vec<BlockId> = self.tip_ids();
        self.add_consensus_timed_turn_v1_with_predecessors(payload, predecessors)
    }

    /// Produce a locally-authored timed turn over an exact round-plan predecessor cohort.
    ///
    /// Round-disciplined federation production must bind the time claim to the same predecessor
    /// set the ordering protocol selected. Validation happens before any local state changes.
    pub fn add_consensus_timed_turn_v1_with_predecessors(
        &mut self,
        payload: ConsensusTimedTurnPayloadV1,
        predecessors: Vec<BlockId>,
    ) -> Result<Block, BlockError> {
        if self.consensus_time_v1.is_none() {
            return Err(BlockError::ConsensusTimePolicyMissing);
        }
        self.try_add_block_with_predecessors(Payload::ConsensusTimedTurnV1(payload), predecessors)
    }

    /// Suggest a bounded signed time claim for an exact predecessor cohort.
    ///
    /// `producer_wall_unix_seconds` is proposal policy only. It is never read by validation or
    /// replay: the returned value is clamped to the authenticated causal interval and becomes
    /// signed block content. Predecessorless blocks always reproduce the deployment anchor exactly,
    /// so independently booting validators cannot mint divergent genesis claims from their clocks.
    pub fn suggest_consensus_time_v1(
        &self,
        predecessors: &[BlockId],
        producer_wall_unix_seconds: i64,
    ) -> Result<i64, BlockError> {
        let policy = self
            .consensus_time_v1
            .ok_or(BlockError::ConsensusTimePolicyMissing)?;
        if predecessors.is_empty() {
            return Ok(policy.genesis_unix_seconds);
        }

        let mut minimum = policy.genesis_unix_seconds;
        for predecessor in predecessors {
            if !self.blocks.contains_key(predecessor) {
                return Err(BlockError::MissingPredecessor {
                    creator: self.self_creator(),
                    seq: self.self_seq.saturating_add(1),
                    missing: *predecessor,
                });
            }
            let frontier = self
                .consensus_time_frontier_v1
                .get(predecessor)
                .copied()
                .ok_or(BlockError::ConsensusTimeFrontierMissing {
                    predecessor: *predecessor,
                })?;
            minimum = minimum.max(frontier);
        }
        let maximum = minimum
            .checked_add(CONSENSUS_TIME_V1_MAX_FORWARD_SECONDS)
            .ok_or(BlockError::ConsensusTimeBoundOverflow)?;
        Ok(producer_wall_unix_seconds.clamp(minimum, maximum))
    }

    /// Deterministically validate one turn payload against authenticated causal time.
    ///
    /// This function never reads wall time. With v1 disabled, a v1 payload fails closed. With v1
    /// enabled, legacy timestamp-less turns fail closed while non-turn DAG traffic remains valid.
    pub fn validate_consensus_time_v1(&self, block: &Block) -> Result<(), BlockError> {
        self.validated_consensus_time_frontier_v1(block).map(drop)
    }

    fn validated_consensus_time_frontier_v1(
        &self,
        block: &Block,
    ) -> Result<Option<i64>, BlockError> {
        let timed = match &block.payload {
            Payload::ConsensusTimedTurnV1(payload) => Some(payload),
            Payload::Turn(_) | Payload::TurnBundle(_) if self.consensus_time_v1.is_some() => {
                return Err(BlockError::LegacyTurnAfterConsensusTimeCutover);
            }
            _ => None,
        };
        let Some(policy) = self.consensus_time_v1 else {
            if timed.is_some() {
                return Err(BlockError::ConsensusTimePolicyMissing);
            }
            return Ok(None);
        };
        let inherited = self.predecessor_consensus_time_frontier_v1(block, policy)?;
        let Some(payload) = timed else {
            // Non-turn blocks carry the inherited frontier through the causal DAG.
            return Ok(Some(inherited));
        };
        payload.validate_shape()?;
        let actual = payload.consensus_time.unix_seconds;
        if block.predecessors.is_empty() {
            if actual != policy.genesis_unix_seconds {
                return Err(BlockError::ConsensusGenesisTimeMismatch {
                    expected: policy.genesis_unix_seconds,
                    actual,
                });
            }
            return Ok(Some(actual));
        }

        if actual < inherited {
            return Err(BlockError::ConsensusTimeRegression {
                minimum: inherited,
                actual,
            });
        }
        let maximum = inherited
            .checked_add(CONSENSUS_TIME_V1_MAX_FORWARD_SECONDS)
            .ok_or(BlockError::ConsensusTimeBoundOverflow)?;
        if actual > maximum {
            return Err(BlockError::ConsensusTimeForwardBound { maximum, actual });
        }
        Ok(Some(actual))
    }

    fn predecessor_consensus_time_frontier_v1(
        &self,
        block: &Block,
        policy: ConsensusTimePolicyV1,
    ) -> Result<i64, BlockError> {
        if block.predecessors.is_empty() {
            return Ok(policy.genesis_unix_seconds);
        }
        let mut maximum = policy.genesis_unix_seconds;
        for id in &block.predecessors {
            if !self.blocks.contains_key(id) {
                return Err(BlockError::MissingPredecessor {
                    creator: block.creator,
                    seq: block.seq,
                    missing: *id,
                });
            }
            let frontier = self
                .consensus_time_frontier_v1
                .get(id)
                .copied()
                .ok_or(BlockError::ConsensusTimeFrontierMissing { predecessor: *id })?;
            maximum = maximum.max(frontier);
        }
        Ok(maximum)
    }

    // ─── Block Reception ─────────────────────────────────────────────────

    /// Receive a block from a peer.
    ///
    /// Verifies signature, checks closure (all predecessors known), and detects
    /// equivocation. Returns `Ok(())` if the block was successfully inserted
    /// (or was already present).
    pub fn receive_block(&mut self, block: Block) -> Result<(), BlockError> {
        let id = block.id();

        // Already have it.
        if self.blocks.contains_key(&id) {
            return Ok(());
        }

        // Verify signature (ed25519 half).
        block.verify_signature()?;

        self.insert_checked(id, block)
    }

    /// Receive a consensus block on the LIVE wire path, PINNING its post-quantum
    /// half to the creator's ENROLLED ML-DSA key.
    ///
    /// This is the hybrid, quantum-resistant reception used by the node's
    /// consensus ingest (`node/src/blocklace_sync.rs`). Unlike [`receive_block`]
    /// (ed25519-only, for local DAG reconstruction and equivocation
    /// bookkeeping), it FAILS CLOSED when the creator is not in the enrolled
    /// roster ([`BlockError::UnenrolledCreator`]) and verifies BOTH signature
    /// halves ([`Block::verify_hybrid`]) — so a quantum adversary who forges the
    /// classical half cannot inject a block under an enrolled member's identity.
    /// The roster is populated out-of-band from the committee via
    /// [`Blocklace::enroll_pq`]; a self-carried PQ key is never trusted.
    pub fn receive_block_pinned(&mut self, block: Block) -> Result<(), BlockError> {
        let id = block.id();

        // Already have it.
        if self.blocks.contains_key(&id) {
            return Ok(());
        }

        // PIN: the creator's post-quantum half MUST verify against the ENROLLED
        // roster key. No enrolled key ⇒ reject fail-closed (never trust a
        // self-carried or on-the-fly-derived key).
        match self.pq_roster.get(&block.creator) {
            Some(enrolled_pq) => block.verify_hybrid(enrolled_pq)?,
            None => {
                return Err(BlockError::UnenrolledCreator {
                    creator: block.creator,
                    seq: block.seq,
                });
            }
        }

        self.insert_checked(id, block)
    }

    /// Shared post-verification reception body: closure check, equivocation
    /// detection (retaining the conflicting block as evidence), tip update, and
    /// ack accounting. Both [`receive_block`] (after the ed25519 check) and
    /// [`receive_block_pinned`] (after the hybrid + pinned check) call this;
    /// `id` is `block.id()` recomputed by the caller.
    fn insert_checked(&mut self, id: BlockId, block: Block) -> Result<(), BlockError> {
        // Check closure: all predecessors must be known.
        for pred in &block.predecessors {
            if !self.blocks.contains_key(pred) {
                return Err(BlockError::MissingPredecessor {
                    creator: block.creator,
                    seq: block.seq,
                    missing: *pred,
                });
            }
        }
        let frontier = self.validated_consensus_time_frontier_v1(&block)?;

        // Check for equivocation.
        if let Some(proof) = self.detect_equivocation(&block) {
            // TWO-TIPS EVIDENCE FLOOR (CM Alg. 1:5): on FIRST detection, pin
            // the incomparable pair as this creator's tips so the next block we
            // author points at BOTH halves and carries the fork into its causal
            // closure — the anchor-relative exclusion predicate needs the pair
            // IN a closure to fire. The old `tips.remove` here left the second
            // half unreferenced forever: evidence that was real and unreachable.
            // A creator already flagged keeps its pinned pair (first pair wins;
            // the bound stays ≤ 2 pointers per creator no matter how many
            // further forks arrive).
            if self.equivocators.insert(block.creator) {
                self.tips
                    .insert(block.creator, CreatorTips::pair(proof.block_a.id(), id));
            }
            // Still insert the block (we keep evidence) but report the equivocation.
            self.blocks.insert(id, block);
            if let Some(frontier) = frontier {
                self.consensus_time_frontier_v1.insert(id, frontier);
            }
            return Err(BlockError::Equivocation {
                creator: proof.creator,
                seq: proof.block_a.seq,
                proof,
            });
        }

        // Don't update tips for known equivocators: a flagged creator's entry is
        // either its frozen evidence pair or (post-weld / external flag) absent.
        if !self.equivocators.contains(&block.creator) {
            // Update tip if this is the highest seq for this creator.
            let should_update_tip = match self.tips.get(&block.creator) {
                Some(current) => {
                    let current_tip = &self.blocks[&current.primary()];
                    block.seq > current_tip.seq
                }
                None => true,
            };
            if should_update_tip {
                self.tips.insert(block.creator, CreatorTips::One(id));
            }
        }

        // Process ack payloads for finality tracking.
        if block.payload == Payload::Ack {
            for pred in &block.predecessors {
                self.finality.record_ack(*pred, block.creator);
            }
        }

        self.blocks.insert(id, block);
        if let Some(frontier) = frontier {
            self.consensus_time_frontier_v1.insert(id, frontier);
        }
        Ok(())
    }

    // ─── CRDT Delta-Merge ────────────────────────────────────────────────

    /// Merge a delta (set of blocks) into our local view.
    ///
    /// The delta must be causally closed: every predecessor in the delta must
    /// either be within the delta itself or already in our blocklace.
    /// Blocks are topologically sorted by the merge process.
    pub fn merge(&mut self, delta: Vec<Block>) -> Result<(), MergeError> {
        // Build a map of delta block IDs for closure checking.
        let delta_ids: HashMap<BlockId, &Block> = delta.iter().map(|b| (b.id(), b)).collect();

        // Check causal closure.
        for block in &delta {
            for pred in &block.predecessors {
                if !self.blocks.contains_key(pred) && !delta_ids.contains_key(pred) {
                    return Err(MergeError::NotCausallyClosed { missing: *pred });
                }
            }
        }

        // Topologically sort the delta so predecessors are inserted first.
        let sorted = topological_sort(&delta, &self.blocks)?;

        // Insert in order.
        for block in sorted {
            let id = block.id();
            // Skip if already present.
            if self.blocks.contains_key(&id) {
                continue;
            }

            // Verify signature.
            block.verify_signature()?;

            let frontier = self.validated_consensus_time_frontier_v1(&block)?;

            // Check for equivocation.
            if let Some(proof) = self.detect_equivocation(&block) {
                // Mirrors `insert_checked` (audit gap C): the creator is
                // flagged so later delta blocks cannot re-populate its tip —
                // and, per the CM Alg. 1:5 evidence floor, the FIRST detected
                // incomparable pair is PINNED as the creator's tips so the next
                // authored block carries the fork into its closure.
                if self.equivocators.insert(block.creator) {
                    self.tips
                        .insert(block.creator, CreatorTips::pair(proof.block_a.id(), id));
                }
                self.blocks.insert(id, block);
                if let Some(frontier) = frontier {
                    self.consensus_time_frontier_v1.insert(id, frontier);
                }
                continue;
            }

            // Don't update tips for known equivocators (mirrors receive_block).
            if !self.equivocators.contains(&block.creator) {
                // Update tip.
                let should_update_tip = match self.tips.get(&block.creator) {
                    Some(current) => {
                        let current_tip = &self.blocks[&current.primary()];
                        block.seq > current_tip.seq
                    }
                    None => true,
                };
                if should_update_tip {
                    self.tips.insert(block.creator, CreatorTips::One(id));
                }
            }

            self.blocks.insert(id, block);
            if let Some(frontier) = frontier {
                self.consensus_time_frontier_v1.insert(id, frontier);
            }
        }

        Ok(())
    }

    // ─── Round Computation (Cordial Miners DAG depth) ────────────────────

    /// Compute Cordial Miners "round" for a single block.
    ///
    /// `round(block) = 1 + max(round(pred))` over the block's predecessors,
    /// or `1` if the block has no predecessors. Bind this into the federation
    /// [`dregg_types::AttestedRoot`] to distinguish forks (closes audit F3).
    ///
    /// This is intentionally a per-block accessor (not a full DAG sweep);
    /// callers wanting the rounds for the whole DAG should iterate.
    pub fn round_of(&self, block_id: &BlockId) -> Option<u64> {
        let block = self.blocks.get(block_id)?;
        if block.predecessors.is_empty() {
            return Some(1);
        }
        // Recursive walk with memoization-free traversal — used per-finalized
        // block, which is sparse, so the O(depth) cost is acceptable.
        let mut stack: Vec<BlockId> = vec![*block_id];
        let mut memo: HashMap<BlockId, u64> = HashMap::new();
        while let Some(id) = stack.last().copied() {
            let b = match self.blocks.get(&id) {
                Some(b) => b,
                None => {
                    stack.pop();
                    continue;
                }
            };
            if b.predecessors.is_empty() {
                memo.insert(id, 1);
                stack.pop();
                continue;
            }
            let mut all_ready = true;
            let mut max_pred = 0u64;
            for pred in &b.predecessors {
                match memo.get(pred) {
                    Some(&r) => max_pred = max_pred.max(r),
                    None => {
                        if self.blocks.contains_key(pred) {
                            stack.push(*pred);
                            all_ready = false;
                        }
                        // Missing predecessor: treat as round 0 contribution
                        // (cannot happen for a closed blocklace, but be
                        // defensive).
                    }
                }
            }
            if all_ready {
                memo.insert(id, 1 + max_pred);
                stack.pop();
            }
        }
        memo.get(block_id).copied()
    }

    // ─── Equivocation Detection ──────────────────────────────────────────

    /// Check if a block equivocates against existing blocks in the blocklace.
    ///
    /// Equivocation (paper Almog–Lewis–Naor–Shapiro arXiv:2402.08068 Def 4.2,
    /// Lean spec `Dregg2/Authority/Blocklace.lean::Equivocation`): two *distinct*
    /// blocks `a, b` by the **same creator** that are **incomparable** under the
    /// happened-before (`≺`, observe) relation — i.e. neither block is in the
    /// other's causal past (`a ⊀ b ∧ b ⊀ a`). The pair is a fork in the
    /// creator's virtual chain.
    ///
    /// This is the *content-independent* definition: it does NOT require the two
    /// blocks to share a sequence number. The earlier `(creator, seq, id≠)`
    /// heuristic is a strict *subset* of this — an equivocator can produce two
    /// incomparable blocks at *different* seq numbers (e.g. fork the chain and
    /// extend one branch) that the seq heuristic misses entirely. We use the
    /// sound incomparability check, reusing the existing `causal_past`
    /// (`≺`) machinery, so every fork is caught regardless of seq.
    ///
    /// Note: a same-seq, same-creator, different-id pair is always incomparable
    /// (two seq-`n` blocks cannot observe each other along an honest virtual
    /// chain, where observation strictly increases seq), so the old cases remain
    /// detected.
    pub fn detect_equivocation(&self, block: &Block) -> Option<EquivocationProof> {
        let id = block.id();

        // The block being ingested is (in general) not yet in `self.blocks`, so
        // `causal_past` cannot resolve it by id. Compute the incoming block's
        // causal past directly from its declared predecessors — these are
        // already present (closure is enforced before detection).
        let block_past = self.causal_past_from_preds(&block.predecessors);

        for (existing_id, existing) in &self.blocks {
            if existing.creator != block.creator || *existing_id == id {
                continue;
            }

            // Incomparability test (paper `a ∥ b ≡ a ⊀ b ∧ b ⊀ a`):
            //   existing ≺ block  ⟺  existing ∈ causal_past(block)
            //   block    ≺ existing ⟺ block ∈ causal_past(existing)
            // If EITHER direction holds the two blocks are causally ordered
            // (honest chain extension), so this is NOT an equivocation.
            let existing_observed_by_block = block_past.contains(existing_id);
            if existing_observed_by_block {
                // existing ≺ block: causally ordered, so not an equivocation. Skipping
                // the second BFS keeps replay of an honest chain O(n²), not O(n³)
                // (a one-creator lace replays every earlier block here; emberian/dregg#101).
                continue;
            }
            let block_observed_by_existing = self.causal_past(existing_id).contains(&id);

            if !existing_observed_by_block && !block_observed_by_existing {
                // Same creator, distinct, mutually non-preceding ⇒ incomparable
                // ⇒ equivocation (the EquivocationProof witness pair).
                return Some(EquivocationProof {
                    creator: block.creator,
                    block_a: existing.clone(),
                    block_b: block.clone(),
                });
            }
        }
        None
    }

    /// Compute the causal past of a (possibly not-yet-inserted) block given its
    /// declared predecessor ids. This is `causal_past` with the seed frontier
    /// supplied directly rather than looked up by block id, so it works for a
    /// block that is mid-ingest and therefore not yet in `self.blocks`.
    fn causal_past_from_preds(&self, predecessors: &[BlockId]) -> HashSet<BlockId> {
        let mut visited = HashSet::new();
        let mut queue: VecDeque<BlockId> = predecessors.iter().copied().collect();

        while let Some(current) = queue.pop_front() {
            if !visited.insert(current) {
                continue;
            }
            if let Some(block) = self.blocks.get(&current) {
                for pred in &block.predecessors {
                    if !visited.contains(pred) {
                        queue.push_back(*pred);
                    }
                }
            }
        }

        visited
    }

    // ─── Query Operations ────────────────────────────────────────────────

    /// Get a creator's virtual chain: all blocks by that creator, sorted by seq.
    pub fn virtual_chain(&self, creator: &[u8; 32]) -> Vec<&Block> {
        let mut chain: Vec<&Block> = self
            .blocks
            .values()
            .filter(|b| &b.creator == creator)
            .collect();
        chain.sort_by_key(|b| b.seq);
        chain
    }

    /// Compute the causal past of a block: all blocks transitively reachable
    /// via predecessors.
    pub fn causal_past(&self, block_id: &BlockId) -> HashSet<BlockId> {
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();

        if let Some(block) = self.blocks.get(block_id) {
            for pred in &block.predecessors {
                queue.push_back(*pred);
            }
        }

        while let Some(current) = queue.pop_front() {
            if !visited.insert(current) {
                continue;
            }
            if let Some(block) = self.blocks.get(&current) {
                for pred in &block.predecessors {
                    if !visited.contains(pred) {
                        queue.push_back(*pred);
                    }
                }
            }
        }

        visited
    }

    /// Compute the union of the causal pasts of several blocks in ONE
    /// shared-visited traversal (instead of re-walking overlapping history once
    /// per block), and INCLUSIVE of each seed id itself. This mirrors the
    /// `crate::Blocklace::causal_past_union` reference impl: each seed is
    /// enqueued (so the seeds are in the result), and unknown ids contribute
    /// only themselves. The single shared visited set makes overlapping
    /// histories cheap — the cost is the size of the union, not the sum of the
    /// per-block pasts.
    pub fn causal_past_union<'a, I>(&self, ids: I) -> HashSet<BlockId>
    where
        I: IntoIterator<Item = &'a BlockId>,
    {
        let mut result = HashSet::new();
        let mut queue: VecDeque<BlockId> = VecDeque::new();
        for id in ids {
            queue.push_back(*id);
        }
        while let Some(current) = queue.pop_front() {
            if !result.insert(current) {
                continue;
            }
            if let Some(block) = self.blocks.get(&current) {
                for pred in &block.predecessors {
                    if !result.contains(pred) {
                        queue.push_back(*pred);
                    }
                }
            }
        }
        result
    }

    /// Check if block `a` is in the causal past of block `b`.
    pub fn is_predecessor(&self, a: &BlockId, b: &BlockId) -> bool {
        if a == b {
            return false;
        }
        self.causal_past(b).contains(a)
    }

    /// Get the current frontier: maximal blocks that no other block points to.
    pub fn frontier(&self) -> Vec<BlockId> {
        let mut pointed_to: HashSet<BlockId> = HashSet::new();
        for block in self.blocks.values() {
            for pred in &block.predecessors {
                pointed_to.insert(*pred);
            }
        }

        self.blocks
            .keys()
            .filter(|id| !pointed_to.contains(id))
            .copied()
            .collect()
    }

    /// Check if `block` observes `target` without observing any equivocation
    /// by `target`'s creator.
    ///
    /// "Observes" means target is in block's causal past (`target ≺ block`).
    /// "Without observing equivocation" means the causal past does not contain a
    /// pair of **incomparable** blocks by the same creator (paper Def 4.2 / Lean
    /// `Blocklace.lean::seesBoth` + `observer_detects`). This is the
    /// content-independent definition: two same-creator blocks in the past that
    /// do not observe each other are a fork, *regardless of sequence number*.
    /// (The earlier same-seq heuristic was a strict subset and missed
    /// different-seq forks.)
    pub fn approved_by(&self, block_id: &BlockId, target_id: &BlockId) -> bool {
        let past = self.causal_past(block_id);

        // target must be in the causal past.
        if !past.contains(target_id) {
            return false;
        }

        // Get the target's creator.
        let target_creator = match self.blocks.get(target_id) {
            Some(b) => b.creator,
            None => return false,
        };

        // Gather the target-creator's blocks visible in the causal past, then
        // check no two of them are incomparable (a fork). Caching each block's
        // causal past avoids recomputing it in the inner loop.
        let creator_blocks: Vec<BlockId> = past
            .iter()
            .filter(|id| {
                self.blocks
                    .get(id)
                    .is_some_and(|b| b.creator == target_creator)
            })
            .copied()
            .collect();

        let pasts: Vec<HashSet<BlockId>> = creator_blocks
            .iter()
            .map(|id| self.causal_past(id))
            .collect();

        for i in 0..creator_blocks.len() {
            for j in (i + 1)..creator_blocks.len() {
                let a = &creator_blocks[i];
                let b = &creator_blocks[j];
                // incomparable: a ⊀ b ∧ b ⊀ a (neither in the other's past).
                let a_observes_b = pasts[i].contains(b);
                let b_observes_a = pasts[j].contains(a);
                if !a_observes_b && !b_observes_a {
                    return false;
                }
            }
        }

        true
    }

    /// Flag a creator as an equivocator on EXTERNAL evidence — evidence this
    /// node does not hold as a local incomparable pair (e.g. a peer-supplied
    /// proof naming blocks we have not received).
    ///
    /// The creator is flagged and its tip entry withdrawn: with no local pair
    /// to pin, there is nothing to carry into a closure, and CM Def. 29
    /// repelling says a node that has observed evidence stops acking the
    /// equivocator's blocks entirely. In-band detection (`insert_checked` /
    /// `merge`), which HOLDS both halves, pins them as a [`CreatorTips::Pair`]
    /// instead so the evidence rides the DAG.
    ///
    /// Returns `true` if this was a newly-flagged equivocator.
    pub fn remove_equivocator(&mut self, creator: &[u8; 32]) -> bool {
        let was_new = self.equivocators.insert(*creator);
        if was_new {
            match self.tips.get(creator) {
                // Never discard locally-held pinned evidence.
                Some(CreatorTips::Pair(_, _)) => {}
                _ => {
                    self.tips.remove(creator);
                }
            }
        }
        was_new
    }

    /// Check if a creator is a known equivocator.
    pub fn is_equivocator(&self, creator: &[u8; 32]) -> bool {
        self.equivocators.contains(creator)
    }

    /// Export all blocks (for delta-merge to a peer).
    pub fn all_blocks(&self) -> Vec<Block> {
        self.blocks.values().cloned().collect()
    }

    /// Export blocks not known to a peer (given a set of known IDs).
    pub fn delta_for(&self, known: &HashSet<BlockId>) -> Vec<Block> {
        self.blocks
            .iter()
            .filter(|(id, _)| !known.contains(id))
            .map(|(_, b)| b.clone())
            .collect()
    }

    /// Iterate over all blocks.
    pub fn iter(&self) -> impl Iterator<Item = (&BlockId, &Block)> {
        self.blocks.iter()
    }

    /// Create a checkpoint of the current blocklace state.
    ///
    /// The checkpoint includes:
    /// - All block data (serialized)
    /// - Current tips per creator
    /// - Detected equivocators
    /// - Ordering state (what has been finalized)
    ///
    /// A new node joining the network can restore from this checkpoint
    /// without replaying the full block history.
    pub fn checkpoint(&self) -> CheckpointData {
        let blocks: Vec<Vec<u8>> = self.blocks.values().map(|b| b.to_bytes()).collect();
        CheckpointData {
            blocks,
            tips: self.tips.clone(),
            equivocators: self.equivocators.iter().copied().collect(),
            ordered_block_ids: self.finality.ordering.ordered.clone(),
            attested_block_ids: self.finality.ordering.attested.iter().copied().collect(),
        }
    }

    /// Restore a blocklace from a checkpoint, **authenticating every block** on
    /// the recovery path exactly as the hardened `receive_block` insert does.
    ///
    /// This is the default loader and the one any **untrusted / peer-supplied**
    /// checkpoint MUST use (e.g. `bootstrap_from_checkpoint`). A checkpoint is
    /// just a bag of serialized blocks; without re-authentication it is an
    /// A1-class recovery-path bypass — a peer could ship a checkpoint containing
    /// a forged block (a block claiming a victim's `creator` with a junk
    /// signature, or one whose predecessor is fiction) and have it sail into the
    /// restored DAG unverified. Here we close that door:
    ///
    /// 1. **Signature** — every block's Ed25519 signature is verified against its
    ///    declared `creator` (rejecting forged/unsigned blocks). Same check as
    ///    `receive_block` step "Verify signature".
    /// 2. **Sequence/closure** — blocks are inserted in topological order; a
    ///    block whose predecessor is absent from the checkpoint (a *dangling*
    ///    predecessor / non-closed view) is rejected. Same check as
    ///    `receive_block` step "Check closure".
    /// 3. **Equivocation** — a same-creator incomparable pair smuggled through
    ///    the checkpoint is detected, the creator recorded as an equivocator, and
    ///    its tip withheld. Same check as `receive_block` step "equivocation".
    ///
    /// `tips`, `equivocators`, and the ordering frontier are then **derived from
    /// the authenticated blocks** rather than copied verbatim from the (untrusted)
    /// checkpoint metadata — a malicious checkpoint cannot assert a tip/ordering
    /// it did not earn. The self-asserted `equivocators` set is folded in as a
    /// lower bound (a checkpoint may declare *more* equivocators than the local
    /// re-derivation observes; it may never *hide* one we detected).
    pub fn from_checkpoint(
        checkpoint: &CheckpointData,
        self_key: SigningKey,
        quorum_threshold: usize,
    ) -> Result<Self, String> {
        let mut lace = Self::new(self_key, quorum_threshold);

        // Deserialize all blocks up front (so we can topo-sort by closure).
        let mut pending: Vec<Block> = Vec::with_capacity(checkpoint.blocks.len());
        for block_bytes in &checkpoint.blocks {
            let block = Block::from_bytes(block_bytes)
                .ok_or_else(|| "failed to deserialize block from checkpoint".to_string())?;
            pending.push(block);
        }

        // (1) Authenticate every block's signature BEFORE it can enter the DAG.
        // A forged/unsigned block claiming a victim creator is rejected here,
        // exactly as the live receive path would reject it.
        for block in &pending {
            block.verify_signature().map_err(|e| {
                format!(
                    "checkpoint block failed signature authentication: {e:?} \
                     (creator={:02x}{:02x}.., seq={})",
                    block.creator[0], block.creator[1], block.seq
                )
            })?;
        }

        // (2)+(3) Insert in topological (closure-respecting) order, rejecting a
        // dangling predecessor and detecting equivocation as we go. We loop,
        // admitting every block whose predecessors are all already present, until
        // either everything is placed or a round makes no progress (⇒ a dangling
        // predecessor, i.e. a non-closed checkpoint — rejected).
        let mut remaining = pending;
        while !remaining.is_empty() {
            let mut progressed = false;
            let mut still_pending: Vec<Block> = Vec::with_capacity(remaining.len());

            for block in remaining.into_iter() {
                let id = block.id();
                if lace.blocks.contains_key(&id) {
                    // Duplicate within the checkpoint — idempotent, drop it.
                    progressed = true;
                    continue;
                }
                let closed = block
                    .predecessors
                    .iter()
                    .all(|pred| lace.blocks.contains_key(pred));
                if !closed {
                    still_pending.push(block);
                    continue;
                }

                // Closure satisfied: run the same equivocation gate as
                // receive_block, then insert. First detection pins the pair
                // (the CM Alg. 1:5 evidence floor), mirroring `insert_checked`
                // — so a restart re-derives a carried-evidence frontier, not a
                // starved one. Which pair gets pinned may differ across
                // re-derivations (map iteration order); any pair satisfies the
                // existential exclusion predicate identically.
                if let Some(proof) = lace.detect_equivocation(&block) {
                    if lace.equivocators.insert(block.creator) {
                        lace.tips
                            .insert(block.creator, CreatorTips::pair(proof.block_a.id(), id));
                    }
                    lace.blocks.insert(id, block);
                } else {
                    if !lace.equivocators.contains(&block.creator) {
                        let should_update_tip = match lace.tips.get(&block.creator) {
                            Some(current) => lace.blocks[&current.primary()].seq < block.seq,
                            None => true,
                        };
                        if should_update_tip {
                            lace.tips.insert(block.creator, CreatorTips::One(id));
                        }
                    }
                    if block.payload == Payload::Ack {
                        for pred in &block.predecessors {
                            lace.finality.record_ack(*pred, block.creator);
                        }
                    }
                    lace.blocks.insert(id, block);
                }
                progressed = true;
            }

            if !progressed {
                // No block in this round could be placed ⇒ at least one has a
                // predecessor that exists nowhere in the checkpoint: a dangling
                // predecessor / non-closed view. Reject the whole checkpoint
                // (the live receive path returns MissingPredecessor here).
                let example = still_pending
                    .first()
                    .map(|b| {
                        format!(
                            "creator={:02x}{:02x}.., seq={}",
                            b.creator[0], b.creator[1], b.seq
                        )
                    })
                    .unwrap_or_default();
                return Err(format!(
                    "checkpoint is not causally closed: {} block(s) have a dangling \
                     predecessor (first: {example})",
                    still_pending.len()
                ));
            }
            remaining = still_pending;
        }

        // Fold the checkpoint's self-asserted equivocators in as a LOWER bound:
        // a checkpoint may name more equivocators than we re-derived (e.g. ones
        // whose evidence blocks were pruned), but it can never hide one we
        // detected above. We never trust it to UN-flag a creator.
        for e in &checkpoint.equivocators {
            if lace.equivocators.insert(*e) {
                // Newly-named equivocator with no locally re-derived pair:
                // withhold its tip (external-evidence repelling, as in
                // `remove_equivocator`). A re-derived pinned pair is kept.
                match lace.tips.get(e) {
                    Some(CreatorTips::Pair(_, _)) => {}
                    _ => {
                        lace.tips.remove(e);
                    }
                }
            }
        }

        // Restore ordering state (finality frontier). These are block-id sets
        // over the now-authenticated `blocks`; an id naming a block we did not
        // admit is simply inert (no unverified block backs it).
        lace.finality.ordering.ordered = checkpoint.ordered_block_ids.clone();
        lace.finality.ordering.attested = checkpoint.attested_block_ids.iter().copied().collect();

        // Derive self_seq from our own (authenticated) tip.
        let self_creator = lace.self_creator();
        if let Some(tip_id) = lace.tips.get(&self_creator).map(CreatorTips::primary)
            && let Some(tip_block) = lace.blocks.get(&tip_id)
        {
            lace.self_seq = tip_block.seq;
        }

        Ok(lace)
    }

    /// Restore a blocklace from a checkpoint **without** re-authenticating blocks.
    ///
    /// This trusts the checkpoint data verbatim (blocks are NOT re-verified
    /// against signatures, closure is NOT enforced, tips/equivocators are copied
    /// as-is — a caller-supplied `equivocators` list can even UN-flag a creator
    /// whose evidence is in the blocks).
    ///
    /// ⚑ **NOT a restart loader. Zero production callers (2026-08-08).** The
    /// node's own restart path (`persist::blocklace_store::load_blocklace`)
    /// routes through the authenticating [`Self::from_checkpoint`]: "it came
    /// from our own local disk" is not provenance — the NODE-1 recovery anchor
    /// exists precisely because an offline attacker can write that disk, and a
    /// restart that trusts what the running path verifies is where node-local
    /// state quietly diverges from committed state (the `auto_evict` reversion
    /// precedent). This verbatim loader remains ONLY for forensic tooling
    /// (`dregg-analyzer` deliberately loads possibly-invalid captures to
    /// analyze them) and for tests that need to CONSTRUCT the untrusted-input
    /// shape. Never wire it into a node boot or a peer sync.
    pub fn from_checkpoint_trusted(
        checkpoint: &CheckpointData,
        self_key: SigningKey,
        quorum_threshold: usize,
    ) -> Result<Self, String> {
        let mut lace = Self::new(self_key, quorum_threshold);

        for block_bytes in &checkpoint.blocks {
            let block = Block::from_bytes(block_bytes)
                .ok_or_else(|| "failed to deserialize block from checkpoint".to_string())?;
            let id = block.id();
            lace.blocks.insert(id, block);
        }

        lace.tips = checkpoint.tips.clone();
        lace.equivocators = checkpoint.equivocators.iter().copied().collect();
        lace.finality.ordering.ordered = checkpoint.ordered_block_ids.clone();
        lace.finality.ordering.attested = checkpoint.attested_block_ids.iter().copied().collect();

        let self_creator = lace.self_creator();
        if let Some(tip_id) = lace.tips.get(&self_creator).map(CreatorTips::primary)
            && let Some(tip_block) = lace.blocks.get(&tip_id)
        {
            lace.self_seq = tip_block.seq;
        }

        Ok(lace)
    }
}

/// Snapshot of the blocklace state for persistence or new-node catch-up.
///
/// ⚑ SCHEMA FLAG DAY (2026-08-08, exclusion-by-past): `tips` is now
/// `CreatorTips` (one tip per honest creator, a pinned evidence PAIR per
/// detected equivocator — the CM Alg. 1:5 two-tips floor). A checkpoint
/// serialized under the old `HashMap<_, BlockId>` shape REFUSES to
/// deserialize; the paired `CANONICAL_STATE_SCHEMA_EPOCH` bump makes the node
/// re-genesis its store rather than reinterpret old bytes.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CheckpointData {
    /// All blocks in serialized form.
    pub blocks: Vec<Vec<u8>>,
    /// Creator -> tips (chain head, or the pinned equivocation-evidence pair).
    pub tips: HashMap<[u8; 32], CreatorTips>,
    /// Known equivocator public keys.
    pub equivocators: Vec<[u8; 32]>,
    /// Block IDs in their total order.
    pub ordered_block_ids: Vec<BlockId>,
    /// Block IDs that have been attested by quorum.
    pub attested_block_ids: Vec<BlockId>,
}

// ─── Helpers ─────────────────────────────────────────────────────────────────

/// Topological sort of blocks, ensuring predecessors come before dependents.
/// Blocks whose predecessors are already in `existing` are considered satisfied.
fn topological_sort(
    blocks: &[Block],
    existing: &HashMap<BlockId, Block>,
) -> Result<Vec<Block>, MergeError> {
    let block_map: HashMap<BlockId, &Block> = blocks.iter().map(|b| (b.id(), b)).collect();
    let mut in_degree: HashMap<BlockId, usize> = HashMap::new();
    let mut dependents: HashMap<BlockId, Vec<BlockId>> = HashMap::new();

    for block in blocks {
        let id = block.id();
        let mut degree = 0;
        for pred in &block.predecessors {
            if !existing.contains_key(pred) {
                // This predecessor is within the delta.
                degree += 1;
                dependents.entry(*pred).or_default().push(id);
            }
        }
        in_degree.insert(id, degree);
    }

    let mut queue: VecDeque<BlockId> = in_degree
        .iter()
        .filter(|&(_, &deg)| deg == 0)
        .map(|(id, _)| *id)
        .collect();

    let mut sorted = Vec::with_capacity(blocks.len());

    while let Some(id) = queue.pop_front() {
        if let Some(block) = block_map.get(&id) {
            sorted.push((*block).clone());
        }
        if let Some(deps) = dependents.get(&id) {
            for dep_id in deps {
                if let Some(deg) = in_degree.get_mut(dep_id) {
                    *deg -= 1;
                    if *deg == 0 {
                        queue.push_back(*dep_id);
                    }
                }
            }
        }
    }

    // If we didn't sort all blocks, there's a missing dependency.
    if sorted.len() < blocks.len() {
        for block in blocks {
            let id = block.id();
            if in_degree.get(&id).copied().unwrap_or(0) > 0 {
                for pred in &block.predecessors {
                    if !existing.contains_key(pred) && !block_map.contains_key(pred) {
                        return Err(MergeError::NotCausallyClosed { missing: *pred });
                    }
                }
            }
        }
    }

    Ok(sorted)
}

// ─── The ML-DSA memo: byte-identity, distinctness, and liveness ───────────────
//
// `Block::new` used to run a full ML-DSA-65 keygen per block, and `Blocklace`
// authored through it and then keyed its tips map with `self_creator()`, which ran
// a SECOND one. Both now read a key derived once, when the `Blocklace` was built.
//
// `creator = H(ed25519 ‖ ml_dsa_pk)` is a CONSENSUS-VISIBLE label. These tests exist
// to make "nothing moved" checkable rather than asserted:
//
//   * byte-identity — the memoised path and the one-shot path agree on every field,
//     and the HYBRID CREATOR of the deterministic test keys matches golden vectors
//     captured from the tree BEFORE this change;
//   * distinctness (the other pole) — a memo that served one identity to everybody
//     would be catastrophic AND would still look fast, so different seeds must give
//     different keys, different creators, and signatures that verify under their own
//     enrolled key and NO other's;
//   * liveness — proven by `Arc::ptr_eq`, never by a stopwatch, so it cannot flake
//     on a loaded box and goes red if the memo is removed.
#[cfg(test)]
mod signer_memo_tests {
    use super::*;
    use crate::signer::HybridBlockSigner;
    use crate::test_committee;

    /// GOLDEN VECTORS, CAPTURED FROM THE PRE-MEMO TREE. For each deterministic test
    /// key `[c; 32]`: its HYBRID creator id `H(ed25519 ‖ ml_dsa_pk)`, and
    /// `blake3(enrolled ML-DSA-65 public key)`.
    ///
    /// Produced by running `Block::hybrid_id` / `Block::pq_public_key` on the tree at
    /// `47d833c03` — i.e. BEFORE the ML-DSA key became a held field — on persvati's
    /// `crewbraid` lane with the Lean-verified keygen core installed.
    ///
    /// This is the assertion that matters most. Every other check in this module
    /// compares the new code against ITSELF; only these compare it against the OLD
    /// code. `creator` is a consensus-visible label and the roster PINS the ML-DSA
    /// key, so a change that moved one byte of either would be a flag day rather
    /// than an optimisation — and it would redden HERE.
    ///
    /// The second column is what makes this sharp: the creator is a HASH of both
    /// public halves, so pinning it alone could in principle be satisfied by a
    /// different pair. Pinning the ML-DSA public key too fixes the DERIVATION, not
    /// just the commitment.
    const GOLDEN: &[(u8, &str, &str)] = &[
        (
            0,
            "0c29ef765c5f8a24ee93d2ff353d26a7f26cc5e81b097094a5d3c535d19a7e86",
            "578afd7e6e199ea6f7541b953c29c94250fed8340ce751694fcd4a011ecc859c",
        ),
        (
            1,
            "5ec846c89771d8c85d1735eebc35a47f22c87a732173089aa31fe1dd534f3012",
            "177c577d91cf59f1008512a5960e280ffc1889d74e10966fa6d6b9d12fbecc3c",
        ),
        (
            3,
            "ff33ae934f9bef2e1ce5d89f8a2b8ef435652e8647da3f4a606c1b9d9eabe9b8",
            "3b60f03fbc3c4e40427bc377a43ab012a1f4c130ba882fe4bccf8f01dc01f0bc",
        ),
        (
            7,
            "425153f6078182fc097ad4e2a4aeeffde4c65983fd592fbd492abd292e5d6649",
            "b470b86b94891081659c41ca43129ca4fd136cd247ecbd0b9d3f037f5215fedd",
        ),
        (
            11,
            "9e2a92c6d310df6b1e4d6d5a2aa7d337b2446875f160c37b1fbb47df2597c89f",
            "a61af21aa0083eb6fcae176022dbd253647cca70309119bd31f31fd09f21c24d",
        ),
        (
            32,
            "202e348c0a103e71c57f989e91e0c8aadd675549c71f9565ad6413264a1e0ced",
            "8e04abbb806697e7ff855df1bce75a4776dbe210f62368bd97e194394c5a1051",
        ),
        (
            64,
            "13557576dfcd16a2483575eaeb6729b751791d22c8d85c863e493cea07a6a360",
            "12763083a706747295661e9f46d8d87ab0e93492dffd7148d311701f409e90fb",
        ),
        (
            200,
            "b5922b868bf892af7f5a013b3ae0300a0862a806c8fb59ae3f26d3ed3907bf72",
            "46258b26d1b5b7c74e6adacdc64a6899a52631a7e70ff4ed2ddd56ef0593a71d",
        ),
    ];

    /// Decode a 32-byte golden hex value.
    fn hex32(s: &str) -> [u8; 32] {
        let mut out = [0u8; 32];
        for (i, byte) in out.iter_mut().enumerate() {
            *byte = u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).expect("golden vector is hex");
        }
        out
    }

    /// ⚑ THE BYTE-IDENTITY PROOF, ACROSS THE CHANGE. The hybrid `creator` and the
    /// enrolled ML-DSA public key a test seed produces today are the ones it
    /// produced before the ML-DSA key was memoised — through the one-shot entry
    /// point AND through the held signer.
    #[test]
    fn hybrid_identity_matches_the_pre_memo_golden_vectors() {
        for (c, creator_hex, pq_hex) in GOLDEN {
            let expected_creator = hex32(creator_hex);
            let expected_pq = hex32(pq_hex);
            let key = test_committee::signing_key(*c);

            assert_eq!(
                Block::hybrid_id(&key),
                expected_creator,
                "the HYBRID creator id of test key [{c}; 32] MOVED. `creator` is a \
                 consensus-visible label — a change here is a flag day, not an optimisation."
            );
            assert_eq!(
                *blake3::hash(&Block::pq_public_key(&key).0).as_bytes(),
                expected_pq,
                "the ENROLLED ML-DSA-65 public key derived from test key [{c}; 32] MOVED — \
                 every roster entry pinning this creator would be invalidated"
            );

            let signer = test_committee::signer(*c);
            assert_eq!(
                signer.creator(),
                expected_creator,
                "the HELD signer for test key [{c}; 32] reports a different creator than the \
                 pre-memo derivation"
            );
            assert_eq!(
                *blake3::hash(&signer.pq_public_key().0).as_bytes(),
                expected_pq,
                "the HELD signer for test key [{c}; 32] enrolls a different ML-DSA public key \
                 than the pre-memo derivation"
            );
        }
    }

    /// ⚑ THE BYTE-IDENTITY PROOF, ACROSS A REAL LACE. A lace authoring through its
    /// HELD identity produces, block for block, exactly the bytes the one-shot
    /// `Block::new` produces from the same bare key.
    ///
    /// Compares every field, including the ed25519 signature and the block `id()`,
    /// over a multi-block strand with real predecessors. The ML-DSA half is compared
    /// by VERIFICATION rather than by bytes, because the crate-fallback signer is
    /// hedged (randomised) — two honest signatures over the same message differ, and
    /// asserting they match would be asserting something FIPS 204 does not promise.
    #[test]
    fn lace_authoring_is_byte_identical_to_the_one_shot() {
        let key = test_committee::signing_key(11);
        let enrolled = Block::pq_public_key(&key);

        let mut lace = Blocklace::new(key.clone(), 1);
        let mut preds: Vec<BlockId> = Vec::new();
        for seq in 1..=4u64 {
            let payload = Payload::Data(vec![seq as u8; 3]);

            // The memoised path: authored by the lace through its held identity.
            let memoised = lace
                .try_add_block_with_predecessors(payload.clone(), preds.clone())
                .expect("local authoring");
            // The one-shot path: a fresh ML-DSA keygen from the same bare seed.
            let one_shot = Block::new(&key, seq, payload, preds.clone());

            assert_eq!(
                memoised.creator, one_shot.creator,
                "seq {seq}: the lace stamped a different HYBRID creator than the one-shot"
            );
            assert_eq!(
                memoised.ed25519, one_shot.ed25519,
                "seq {seq}: ed25519 half"
            );
            assert_eq!(memoised.seq, one_shot.seq, "seq {seq}: sequence");
            assert_eq!(memoised.payload, one_shot.payload, "seq {seq}: payload");
            assert_eq!(
                memoised.predecessors, one_shot.predecessors,
                "seq {seq}: predecessors"
            );
            assert_eq!(
                memoised.signature, one_shot.signature,
                "seq {seq}: the ed25519 signature differs — ed25519 is deterministic \
                 (RFC 8032), so this means the SIGNED CONTENT differs"
            );
            assert_eq!(
                memoised.id(),
                one_shot.id(),
                "seq {seq}: the canonical block id differs"
            );

            // Both PQ halves verify under the SAME enrolled key, over their own id.
            assert!(
                memoised.verify_hybrid(&enrolled).is_ok(),
                "seq {seq}: the memoised block does not verify under the enrolled key"
            );
            assert!(
                one_shot.verify_hybrid(&enrolled).is_ok(),
                "seq {seq}: the one-shot block does not verify under the enrolled key"
            );

            preds = vec![memoised.id()];
        }
    }

    /// The held signer agrees with all three bare-key entry points it replaced.
    #[test]
    fn signer_path_is_byte_identical_to_the_one_shot() {
        for c in [0u8, 3, 64, 200] {
            let key = test_committee::signing_key(c);
            let signer = HybridBlockSigner::new(key.clone());

            assert_eq!(
                signer.creator(),
                Block::hybrid_id(&key),
                "creator [{c}; 32]"
            );
            assert_eq!(
                signer.ed25519(),
                key.verifying_key().to_bytes(),
                "ed25519 [{c}; 32]"
            );
            assert_eq!(
                signer.pq_public_key().0,
                Block::pq_public_key(&key).0,
                "enrolled ML-DSA public key [{c}; 32]"
            );

            let memoised = Block::new_signed_by(&signer, 5, Payload::Ack, vec![]);
            let one_shot = Block::new(&key, 5, Payload::Ack, vec![]);
            assert_eq!(memoised.creator, one_shot.creator);
            assert_eq!(memoised.signature, one_shot.signature);
            assert_eq!(memoised.id(), one_shot.id());
        }
    }

    /// ⚑ THE OTHER POLE. Four identities driven INTERLEAVED through their own laces:
    /// a memo that returned ONE key for everybody would be catastrophic and would
    /// still look fast, so this is the check that a speedup did not become a
    /// collapse.
    ///
    /// Interleaving matters: it is the order that a shared-slot memo would corrupt.
    /// Then the falsifier goes on the wire — each block verifies under its OWN
    /// creator's enrolled key and under NO other's.
    #[test]
    fn four_identities_never_share_a_derived_pq_key() {
        let ids = [21u8, 22, 23, 24];
        let mut laces: Vec<Blocklace> = ids
            .iter()
            .map(|c| Blocklace::new(test_committee::signing_key(*c), 1))
            .collect();
        let enrolled: Vec<crate::pq::MlDsaPublicKey> = ids
            .iter()
            .map(|c| Block::pq_public_key(&test_committee::signing_key(*c)))
            .collect();

        // Every identity's public halves are distinct.
        for i in 0..ids.len() {
            for j in (i + 1)..ids.len() {
                assert_ne!(
                    laces[i].self_creator(),
                    laces[j].self_creator(),
                    "identities {} and {} share a HYBRID creator id",
                    ids[i],
                    ids[j]
                );
                // Compared by digest: an `assert_ne!` on the raw 1952-byte keys dumps
                // both of them into the failure output and buries the message.
                assert_ne!(
                    blake3::hash(&enrolled[i].0),
                    blake3::hash(&enrolled[j].0),
                    "identities {} and {} derived the SAME ML-DSA public key — the memo is \
                     serving one identity to everybody",
                    ids[i],
                    ids[j]
                );
            }
        }

        // INTERLEAVED authoring: round-robin, two rounds each.
        let mut blocks: Vec<Vec<Block>> = vec![Vec::new(); ids.len()];
        for _round in 0..2 {
            for (i, lace) in laces.iter_mut().enumerate() {
                let b = lace.add_block(Payload::Data(vec![ids[i]]));
                blocks[i].push(b);
            }
        }

        // THE FALSIFIER, on the wire: each block verifies under its OWN enrolled key
        // and under NO other identity's.
        for (i, own_blocks) in blocks.iter().enumerate() {
            for block in own_blocks {
                assert_eq!(
                    block.creator,
                    enrolled_creator(ids[i]),
                    "identity {} authored under the wrong creator",
                    ids[i]
                );
                assert!(
                    block.verify_hybrid(&enrolled[i]).is_ok(),
                    "identity {}'s block does not verify under its OWN enrolled key",
                    ids[i]
                );
                for (j, other) in enrolled.iter().enumerate() {
                    if i == j {
                        continue;
                    }
                    assert!(
                        block.verify_hybrid(other).is_err(),
                        "identity {}'s block ALSO verified under identity {}'s enrolled key — \
                         two identities are sharing one derived ML-DSA key",
                        ids[i],
                        ids[j]
                    );
                }
            }
        }
    }

    /// The hybrid creator of test key `[c; 32]`, via the one-shot path.
    fn enrolled_creator(c: u8) -> [u8; 32] {
        Block::hybrid_id(&test_committee::signing_key(c))
    }

    /// ⚑ THE MEMO IS LIVE, proven by OBJECT IDENTITY rather than by a stopwatch.
    ///
    /// A lace that authors four blocks reads the SAME `Arc<MlDsaSigningKey>` every
    /// time. This is what goes red if someone reverts `Blocklace` to a bare
    /// `SigningKey` and re-derives per block: the timings would regress silently,
    /// but this assertion cannot.
    #[test]
    fn a_lace_derives_its_pq_key_once_however_many_blocks_it_authors() {
        let mut lace = Blocklace::new(test_committee::signing_key(31), 1);
        let first = std::sync::Arc::clone(lace.signer().pq_handle());

        for _ in 0..4 {
            lace.add_block(Payload::Ack);
            assert!(
                std::sync::Arc::ptr_eq(&first, lace.signer().pq_handle()),
                "the lace re-derived its ML-DSA key while authoring — the memo is not live"
            );
        }

        // And a CLONE of the lace (the node's `poll_finalized_blocks` snapshot path)
        // shares the key rather than deriving a second one.
        let snapshot = lace.clone();
        assert!(
            std::sync::Arc::ptr_eq(&first, snapshot.signer().pq_handle()),
            "cloning a Blocklace re-derived its ML-DSA key — the snapshot path pays a keygen"
        );
        assert_eq!(snapshot.self_creator(), lace.self_creator());
    }

    /// The signer's `Arc` fields must not cost `Blocklace` its auto traits: the node
    /// holds a lace across `await` points and SNAPSHOTS it by `clone` for
    /// `poll_finalized_blocks`. `Arc<T>` is `Send + Sync` only when `T` is, so a
    /// non-`Sync` key type would silently break every async consumer — a compile
    /// error far from here, or none at all until someone spawns.
    #[test]
    fn signer_and_lace_stay_send_and_sync() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<HybridBlockSigner>();
        assert_send_sync::<Blocklace>();
        assert_send_sync::<crate::dissemination::Disseminator>();
    }

    /// A `Disseminator` derives its identity once, however many blocks it authors.
    #[test]
    fn a_disseminator_derives_its_pq_key_once() {
        use crate::dissemination::Disseminator;

        let signer = test_committee::signer(41).clone();
        let handle = std::sync::Arc::clone(signer.pq_handle());
        let mut d = Disseminator::with_signer(signer);

        for i in 0..4u8 {
            let block = d.create_block(vec![i]);
            assert_eq!(block.creator, test_committee::signer(41).ed25519());
        }
        assert!(
            std::sync::Arc::ptr_eq(&handle, test_committee::signer(41).pq_handle()),
            "the disseminator's identity was re-derived"
        );
    }
}

// ─── HYBRID PQ (ed25519 ∧ ML-DSA-65) enroll+PIN tests ─────────────────────────
#[cfg(test)]
mod pq_hybrid_tests {
    use super::*;
    use crate::pq;
    use ed25519_dalek::{Signer, SigningKey};

    /// Deterministic per-index test key (mirrors the strand-layer test helper).
    fn key_for(i: u8) -> SigningKey {
        SigningKey::from_bytes(&[i; 32])
    }

    /// A blocklace whose committee (members 1..=8) is pre-enrolled in the
    /// ML-DSA roster, so the pinned live path can verify their blocks.
    fn enrolled_lace() -> Blocklace {
        let mut lace = Blocklace::new(key_for(1), 3);
        for c in 1..=8u8 {
            let k = key_for(c);
            // Roster is keyed by the HYBRID id (== the block's `creator`).
            lace.enroll_pq(Block::hybrid_id(&k), Block::pq_public_key(&k));
        }
        lace
    }

    /// An honest hybrid consensus block — both halves from the creator's
    /// from-seed keys — passes `verify_hybrid` and the pinned live path.
    #[test]
    fn hybrid_honest_block_passes() {
        let creator = key_for(7);
        let enrolled = Block::pq_public_key(&creator);
        let block = Block::new(&creator, 1, Payload::Data(b"honest".to_vec()), vec![]);
        assert!(block.is_signed_hybrid(), "carries both halves");
        assert!(
            !block.pq_signature.is_empty(),
            "PQ half present (~{} bytes)",
            pq::SIG_LEN
        );
        assert!(block.verify_hybrid(&enrolled).is_ok());

        let mut lace = enrolled_lace();
        assert!(lace.receive_block_pinned(block).is_ok());
        assert_eq!(lace.len(), 1);
    }

    /// F2 (self-equivocation window): `rollback_local_authored` is the EXACT
    /// inverse of authoring, so a block that failed to persist durably can be
    /// withdrawn from the live lace before broadcast. Both directions: a
    /// second-block rollback restores the prior self-tip + seq; a genesis-block
    /// rollback withdraws the tip and returns seq to 0.
    #[test]
    fn rollback_local_authored_restores_seq_and_tip() {
        let mut lace = enrolled_lace(); // self = key_for(1)
        let self_creator = lace.self_creator();
        assert_eq!(lace.self_seq, 0);
        assert!(lace.tips.get(&self_creator).is_none());

        let b1 = lace.add_block(Payload::Ack);
        assert_eq!(lace.self_seq, 1);
        assert_eq!(
            lace.tips.get(&self_creator),
            Some(&CreatorTips::One(b1.id()))
        );
        let b2 = lace.add_block(Payload::Data(b"x".to_vec()));
        assert_eq!(lace.self_seq, 2);
        assert_eq!(
            lace.tips.get(&self_creator),
            Some(&CreatorTips::One(b2.id()))
        );
        assert!(lace.blocks.contains_key(&b2.id()));

        // Roll back the second (un-persisted) block: seq → 1, tip → b1, b2 gone.
        assert!(lace.rollback_local_authored(b2.id()));
        assert_eq!(
            lace.self_seq, 1,
            "self_seq restored to the prior authored seq"
        );
        assert_eq!(
            lace.tips.get(&self_creator),
            Some(&CreatorTips::One(b1.id())),
            "tip restored to the prior self block"
        );
        assert!(
            !lace.blocks.contains_key(&b2.id()),
            "the un-persisted block is withdrawn"
        );

        // Re-authoring yields seq 2 again — live state matches what boot would
        // rebuild from persisted blocks (b1 only), so no (creator, seq) reuse.
        let b2b = lace.add_block(Payload::Data(b"y".to_vec()));
        assert_eq!(b2b.seq, 2);

        // Roll back to the genesis boundary: the tip is withdrawn, seq → 0.
        assert!(lace.rollback_local_authored(b2b.id()));
        assert!(lace.rollback_local_authored(b1.id()));
        assert_eq!(lace.self_seq, 0, "seq returns to genesis");
        assert!(
            lace.tips.get(&self_creator).is_none(),
            "no self tip after genesis rollback"
        );
        assert!(lace.blocks.is_empty(), "no self blocks remain");
    }

    /// `rollback_local_authored` NEVER touches a superseded or unknown block: it
    /// only ever withdraws our OWN current tip (a no-op false otherwise), so it
    /// cannot corrupt the strand if misapplied.
    #[test]
    fn rollback_local_authored_refuses_non_tip() {
        let mut lace = enrolled_lace();
        let b1 = lace.add_block(Payload::Ack);
        let b2 = lace.add_block(Payload::Ack);
        let seq_before = lace.self_seq;

        // b1 is superseded by b2 (the tip) → refuse, no mutation.
        assert!(
            !lace.rollback_local_authored(b1.id()),
            "refuse to roll back a superseded block"
        );
        assert_eq!(lace.self_seq, seq_before, "no mutation on refusal");
        assert!(lace.blocks.contains_key(&b1.id()));
        assert!(lace.blocks.contains_key(&b2.id()));

        // A totally unknown id is a no-op too.
        assert!(!lace.rollback_local_authored(BlockId([0xEE; 32])));
        assert_eq!(lace.self_seq, seq_before);
    }

    /// THE adversarial test: a consensus block with a VALID ed25519 half from
    /// committee member P, but an ML-DSA half signed under an ATTACKER's OWN
    /// fresh key (≠ P's enrolled key) MUST be rejected. The quantum-adversary
    /// scenario: assume the classical half is forgeable, but the PQ half is
    /// pinned to P's enrolled key, which the attacker does not hold.
    #[test]
    fn hybrid_attacker_pq_key_rejected() {
        let p_key = key_for(7); // committee member P
        let p_enrolled = Block::pq_public_key(&p_key); // P's ENROLLED ML-DSA key

        // Honest-looking block: valid ed25519 half by P over its signing content.
        let mut forged = Block::new(&p_key, 1, Payload::Data(b"inject".to_vec()), vec![]);
        // (Block::new already produced P's genuine ed25519 half; re-affirm it.)
        let content = Block::signing_content(
            &forged.creator,
            forged.seq,
            &forged.payload,
            &forged.predecessors,
        );
        forged.signature = p_key.sign(&content).to_bytes();

        // The ATTACKER controls the PQ half but NOT P's from-seed ML-DSA key:
        // they generate their own ML-DSA key (a different seed) and sign id().
        let attacker_seed = [0xAB_u8; 32];
        let (attacker_pq_pub, attacker_pq_sk) = pq::MlDsaSigningKey::from_seed(&attacker_seed);
        forged.pq_signature = attacker_pq_sk.sign(&forged.id().0).unwrap();
        assert_ne!(
            attacker_pq_pub, p_enrolled,
            "attacker key must differ from P's enrolled key"
        );

        // The forged PQ half is a VALID ML-DSA signature — under the ATTACKER's
        // key — so it MUST NOT verify against P's ENROLLED key.
        assert!(
            attacker_pq_pub.verify(&forged.id().0, &forged.pq_signature),
            "sanity: forged sig is valid under the attacker's own key"
        );
        match forged.verify_hybrid(&p_enrolled) {
            Err(BlockError::BadPqSignature { .. }) => {}
            other => panic!("expected BadPqSignature, got {other:?}"),
        }

        // And it is rejected by the pinned live reception path.
        let mut lace = enrolled_lace();
        match lace.receive_block_pinned(forged) {
            Err(BlockError::BadPqSignature { .. }) => {}
            other => panic!("expected BadPqSignature on insert, got {other:?}"),
        }
        assert_eq!(lace.len(), 0, "forged block must not be stored");
    }

    /// THE COMMITMENT ADVERSARIAL TEST (out-of-band → cryptographic upgrade): an
    /// attacker who KEEPS the honest member P's ed25519 key but presents their OWN
    /// ML-DSA key is rejected by the identity commitment — the `creator` id binds
    /// BOTH public halves, so a swapped ML-DSA key no longer recomputes to
    /// `creator`, and forming a fresh id that reuses P's ed25519 key is simply a
    /// DIFFERENT (unenrolled) identity, never P.
    #[test]
    fn hybrid_commitment_rejects_swapped_ml_dsa() {
        let p_key = key_for(7);
        let p_enrolled = Block::pq_public_key(&p_key); // P's committed ML-DSA key
        let block = Block::new(&p_key, 1, Payload::Data(b"x".to_vec()), vec![]);
        // The id genuinely commits to (P_ed, P_mldsa).
        assert!(block.verify_hybrid(&p_enrolled).is_ok());
        assert!(dregg_types::verify_committed_ml_dsa(
            &block.creator,
            &block.ed25519,
            &p_enrolled.0
        ));

        // Attacker keeps P's ed25519 key but presents their OWN ML-DSA key: the
        // commitment does NOT recompute to `creator`, so verify rejects BEFORE any
        // signature is checked.
        let (attacker_mldsa, _sk) = pq::MlDsaSigningKey::from_seed(&[0xCD_u8; 32]);
        assert_ne!(attacker_mldsa, p_enrolled);
        assert!(!dregg_types::verify_committed_ml_dsa(
            &block.creator,
            &block.ed25519,
            &attacker_mldsa.0
        ));
        match block.verify_hybrid(&attacker_mldsa) {
            Err(BlockError::BadPqSignature { .. }) => {}
            other => panic!("commitment gate must reject a swapped ML-DSA key, got {other:?}"),
        }

        // Forming a fresh id that REUSES P's ed25519 key is a DISTINCT creator —
        // not P — so on the pinned live path it is UnenrolledCreator (it never
        // inherits P's enrolled slot).
        let attacker_creator = Block::hybrid_id_from_parts(&block.ed25519, &attacker_mldsa);
        assert_ne!(
            attacker_creator, block.creator,
            "reusing P's ed25519 key yields a distinct hybrid id"
        );
        let mut forged = block.clone();
        forged.creator = attacker_creator;
        let mut lace = enrolled_lace();
        match lace.receive_block_pinned(forged) {
            Err(BlockError::UnenrolledCreator { .. }) => {}
            other => panic!("a reused-ed25519 identity must be UnenrolledCreator, got {other:?}"),
        }
        assert_eq!(lace.len(), 0);
    }

    /// A block with a missing / empty PQ half fails CLOSED — never treated as a
    /// valid ed25519-only block on the pinned path.
    #[test]
    fn hybrid_missing_pq_half_fails_closed() {
        let p_key = key_for(7);
        let enrolled = Block::pq_public_key(&p_key);

        let mut ed_only = Block::new(&p_key, 1, Payload::Data(b"x".to_vec()), vec![]);
        ed_only.pq_signature.clear(); // strip the PQ half
        assert!(!ed_only.is_signed_hybrid());
        match ed_only.verify_hybrid(&enrolled) {
            Err(BlockError::UnsignedPq { .. }) => {}
            other => panic!("expected UnsignedPq (fail-closed), got {other:?}"),
        }
        let mut lace = enrolled_lace();
        match lace.receive_block_pinned(ed_only) {
            Err(BlockError::UnsignedPq { .. }) => {}
            other => panic!("expected UnsignedPq on insert, got {other:?}"),
        }
        assert_eq!(lace.len(), 0);
    }

    /// A creator with NO enrolled ML-DSA key is rejected fail-closed — the
    /// pinned path never trusts a self-carried or on-the-fly-derived PQ key.
    #[test]
    fn hybrid_unenrolled_creator_rejected() {
        // A fully-valid hybrid block by creator 200, but enrolled_lace only
        // enrolls members 1..=8.
        let block = Block::new(
            &key_for(200),
            1,
            Payload::Data(b"stranger".to_vec()),
            vec![],
        );
        assert!(block.is_signed_hybrid());
        let mut lace = enrolled_lace();
        match lace.receive_block_pinned(block) {
            Err(BlockError::UnenrolledCreator { .. }) => {}
            other => panic!("expected UnenrolledCreator, got {other:?}"),
        }
        assert_eq!(lace.len(), 0);
    }

    /// The ed25519-only `receive_block` still accepts an honest block (the
    /// hybrid pin is an ADDITIVE live-path gate; local DAG reconstruction and
    /// the 41 existing reception tests are unaffected).
    #[test]
    fn ed25519_only_receive_block_still_accepts() {
        let block = Block::new(&key_for(3), 1, Payload::Data(b"local".to_vec()), vec![]);
        let mut lace = Blocklace::new(key_for(1), 3);
        assert!(lace.receive_block(block).is_ok());
        assert_eq!(lace.len(), 1);
    }
}
