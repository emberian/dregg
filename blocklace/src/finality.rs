//! Core blocklace data structure: a DAG of signed blocks with equivocation detection.
//!
//! Based on arXiv:2402.08068. The blocklace is a partially-ordered set of signed
//! blocks, where each block contains hash-pointers to its predecessors. Each
//! participant maintains a local view that grows monotonically via CRDT union-merge.

use std::collections::{HashMap, HashSet, VecDeque};

use ed25519_dalek::{Signer, SigningKey, Verifier, VerifyingKey};
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
    /// An acknowledgment (I've seen these blocks).
    Ack,
    /// A checkpoint (federation root at this height).
    Checkpoint { root: [u8; 32], height: u64 },
    /// A membership vote (join/leave).
    MembershipVote { action: MembershipAction },
    /// Generic application data.
    Data(Vec<u8>),
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
    Join { node_id: [u8; 32] },
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
    /// The creator's public key (Ed25519 compressed point).
    pub creator: [u8; 32],
    /// Sequence number within this creator's virtual chain.
    pub seq: u64,
    /// The block's payload.
    pub payload: Payload,
    /// Hash pointers to predecessor blocks (what this block "sees").
    pub predecessors: Vec<BlockId>,
    /// Ed25519 signature over (creator, seq, payload_hash, predecessors).
    #[serde(with = "crate::serde_sig64")]
    pub signature: [u8; 64],
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
#[derive(Clone, Debug)]
pub struct EquivocationProof {
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
        let mut buf = Vec::with_capacity(18 + 32 + 8 + 32 + predecessors.len() * 32);
        buf.extend_from_slice(b"dregg-blocklace-v1");
        buf.extend_from_slice(creator);
        buf.extend_from_slice(&seq.to_le_bytes());
        // Hash the payload to keep the signed content compact.
        let payload_hash = blake3::hash(&Self::payload_bytes(payload));
        buf.extend_from_slice(payload_hash.as_bytes());
        for pred in predecessors {
            buf.extend_from_slice(&pred.0);
        }
        buf
    }

    /// Serialize a payload into bytes for hashing (deterministic).
    fn payload_bytes(payload: &Payload) -> Vec<u8> {
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
                    MembershipAction::Join { node_id } => {
                        buf.push(0x01);
                        buf.extend_from_slice(node_id);
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

    /// Verify this block's Ed25519 signature.
    pub fn verify_signature(&self) -> Result<(), BlockError> {
        let content =
            Self::signing_content(&self.creator, self.seq, &self.payload, &self.predecessors);
        let verifying_key =
            VerifyingKey::from_bytes(&self.creator).map_err(|_| BlockError::InvalidSignature {
                creator: self.creator,
                seq: self.seq,
            })?;
        let signature = ed25519_dalek::Signature::from_bytes(&self.signature);
        verifying_key
            .verify(&content, &signature)
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

    /// Create and sign a new block.
    pub fn new(
        signing_key: &SigningKey,
        seq: u64,
        payload: Payload,
        predecessors: Vec<BlockId>,
    ) -> Self {
        let creator: [u8; 32] = signing_key.verifying_key().to_bytes();
        let content = Self::signing_content(&creator, seq, &payload, &predecessors);
        let signature = signing_key.sign(&content);
        Block {
            creator,
            seq,
            payload,
            predecessors,
            signature: signature.to_bytes(),
        }
    }
}

// ─── Finality Tracker ────────────────────────────────────────────────────────

/// Tracks finality progression for blocks in the blocklace.
///
/// As blocks accumulate acknowledgments from other participants, they progress
/// through finality levels: Local -> Bilateral -> Ordered -> Attested.
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

/// The blocklace: a local view of the global DAG.
///
/// Each node maintains its own Blocklace instance. The blocklace grows monotonically
/// via CRDT union-merge: receiving blocks from peers can only add to the local view,
/// never remove.
pub struct Blocklace {
    /// All known blocks.
    pub(crate) blocks: HashMap<BlockId, Block>,
    /// Per-creator tip tracking (latest block per creator).
    tips: HashMap<[u8; 32], BlockId>,
    /// Detected equivocators.
    equivocators: HashSet<[u8; 32]>,
    /// Our own signing key.
    self_key: SigningKey,
    /// Our own sequence counter.
    self_seq: u64,
    /// Finality tracking.
    pub finality: FinalityTracker,
}

impl Blocklace {
    /// Create a new blocklace with the given signing key and quorum threshold.
    pub fn new(self_key: SigningKey, quorum_threshold: usize) -> Self {
        Blocklace {
            blocks: HashMap::new(),
            tips: HashMap::new(),
            equivocators: HashSet::new(),
            self_key,
            self_seq: 0,
            finality: FinalityTracker::new(quorum_threshold),
        }
    }

    /// Create a blocklace without finality tracking (quorum = 1, for testing).
    pub fn new_simple(self_key: SigningKey) -> Self {
        Self::new(self_key, 1)
    }

    /// Our own public key.
    pub fn self_creator(&self) -> [u8; 32] {
        self.self_key.verifying_key().to_bytes()
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

    /// Get current tips (latest known block per creator).
    pub fn tips(&self) -> &HashMap<[u8; 32], BlockId> {
        &self.tips
    }

    /// Get a reference to the signing key.
    pub fn signing_key(&self) -> &SigningKey {
        &self.self_key
    }

    // ─── Block Creation ──────────────────────────────────────────────────

    /// Create a new block with the given payload.
    /// Predecessors = all current tips (what we currently know about).
    pub fn add_block(&mut self, payload: Payload) -> Block {
        self.self_seq += 1;
        let predecessors: Vec<BlockId> = self.tips.values().copied().collect();
        let block = Block::new(&self.self_key, self.self_seq, payload, predecessors);
        let id = block.id();
        self.blocks.insert(id, block.clone());
        self.tips.insert(self.self_creator(), id);
        block
    }

    /// Create a new block with explicit predecessors (for advanced usage).
    pub fn add_block_with_predecessors(
        &mut self,
        payload: Payload,
        predecessors: Vec<BlockId>,
    ) -> Block {
        self.self_seq += 1;
        let block = Block::new(&self.self_key, self.self_seq, payload, predecessors);
        let id = block.id();
        self.blocks.insert(id, block.clone());
        self.tips.insert(self.self_creator(), id);
        block
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

        // Verify signature.
        block.verify_signature()?;

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

        // Check for equivocation.
        if let Some(proof) = self.detect_equivocation(&block) {
            self.equivocators.insert(block.creator);
            self.tips.remove(&block.creator);
            // Still insert the block (we keep evidence) but report the equivocation.
            self.blocks.insert(id, block);
            return Err(BlockError::Equivocation {
                creator: proof.creator,
                seq: proof.block_a.seq,
                proof,
            });
        }

        // Don't update tips for known equivocators.
        if !self.equivocators.contains(&block.creator) {
            // Update tip if this is the highest seq for this creator.
            let should_update_tip = match self.tips.get(&block.creator) {
                Some(current_tip_id) => {
                    let current_tip = &self.blocks[current_tip_id];
                    block.seq > current_tip.seq
                }
                None => true,
            };
            if should_update_tip {
                self.tips.insert(block.creator, id);
            }
        }

        // Process ack payloads for finality tracking.
        if block.payload == Payload::Ack {
            for pred in &block.predecessors {
                self.finality.record_ack(*pred, block.creator);
            }
        }

        self.blocks.insert(id, block);
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

            // Check for equivocation.
            if let Some(proof) = self.detect_equivocation(&block) {
                // Closes audit gap C in AUDIT-blocklace-consensus.md: merge()
                // must mirror receive_block() and remove the equivocator's
                // tip. Without this, subsequent blocks from the equivocator
                // in the same delta could update tips for a creator we now
                // know to be Byzantine — leaving stale tip state for the
                // dissemination/frontier and multi-group block-creation
                // codepaths to consume.
                self.equivocators.insert(block.creator);
                self.tips.remove(&block.creator);
                self.blocks.insert(id, block);
                let _ = proof;
                continue;
            }

            // Don't update tips for known equivocators (mirrors receive_block).
            if !self.equivocators.contains(&block.creator) {
                // Update tip.
                let should_update_tip = match self.tips.get(&block.creator) {
                    Some(current_tip_id) => {
                        let current_tip = &self.blocks[current_tip_id];
                        block.seq > current_tip.seq
                    }
                    None => true,
                };
                if should_update_tip {
                    self.tips.insert(block.creator, id);
                }
            }

            self.blocks.insert(id, block);
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

    /// Remove an equivocator from the blocklace.
    ///
    /// This marks the creator as an equivocator (if not already) and removes
    /// their blocks from the tips map. The blocks themselves are retained as
    /// evidence, but the equivocator will not be considered for tip tracking
    /// or future operations.
    ///
    /// Returns `true` if this was a newly-detected equivocator.
    pub fn remove_equivocator(&mut self, creator: &[u8; 32]) -> bool {
        let was_new = self.equivocators.insert(*creator);
        self.tips.remove(creator);
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

    /// Restore a blocklace from a checkpoint.
    ///
    /// This trusts the checkpoint data (blocks are NOT re-verified against
    /// signatures). Use only for trusted checkpoint sources (e.g., local disk,
    /// or after verifying the checkpoint's own signature/hash).
    pub fn from_checkpoint(
        checkpoint: &CheckpointData,
        self_key: SigningKey,
        quorum_threshold: usize,
    ) -> Result<Self, String> {
        let mut lace = Self::new(self_key, quorum_threshold);

        // Restore blocks (order doesn't matter since we skip closure checks).
        for block_bytes in &checkpoint.blocks {
            let block = Block::from_bytes(block_bytes)
                .ok_or_else(|| "failed to deserialize block from checkpoint".to_string())?;
            let id = block.id();
            lace.blocks.insert(id, block);
        }

        // Restore tips.
        lace.tips = checkpoint.tips.clone();

        // Restore equivocators.
        lace.equivocators = checkpoint.equivocators.iter().copied().collect();

        // Restore ordering state.
        lace.finality.ordering.ordered = checkpoint.ordered_block_ids.clone();
        lace.finality.ordering.attested = checkpoint.attested_block_ids.iter().copied().collect();

        // Restore self_seq from our own tip.
        let self_creator = lace.self_creator();
        if let Some(tip_id) = lace.tips.get(&self_creator) {
            if let Some(tip_block) = lace.blocks.get(tip_id) {
                lace.self_seq = tip_block.seq;
            }
        }

        Ok(lace)
    }
}

/// Snapshot of the blocklace state for persistence or new-node catch-up.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CheckpointData {
    /// All blocks in serialized form.
    pub blocks: Vec<Vec<u8>>,
    /// Creator -> tip block ID.
    pub tips: HashMap<[u8; 32], BlockId>,
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
