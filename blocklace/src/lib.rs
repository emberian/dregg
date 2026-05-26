//! # dregg-blocklace
//!
//! # Trust Model
//!
//! This crate operates at the **CONSENSUS-TRUSTLESS** trust level.
//!
//! - **Soundness**: Finality is verified by ALL participants. Once a block reaches
//!   finality (via the constitution's supermajority rule), it cannot be reverted without
//!   violating the BFT assumption (>1/3 Byzantine). The DAG structure is self-validating:
//!   hash links make it impossible to rewrite history without detection.
//! - **Assumptions**: Honest supermajority (2f+1 of 3f+1 nodes). Network eventually
//!   delivers messages (partial synchrony). Block creators sign their blocks (Ed25519).
//!   BLAKE3 is collision-resistant (for content addressing).
//! - **Verifiable by**: Every participant independently. Any node can verify:
//!   - Block integrity (hash matches content)
//!   - Block authenticity (signature matches creator)
//!   - Causal ordering (all predecessors exist and are valid)
//!   - Finality (supermajority acknowledgment per the constitution)
//!
//! ## Trust Boundaries
//! - The blocklace does NOT verify payload semantics (that is the executor's job)
//! - The blocklace DOES guarantee total ordering and finality
//! - Dissemination is best-effort (liveness) but does not affect safety
//!
//! ## Key Invariants
//! 1. A block's ID is a deterministic function of its content (content-addressed)
//! 2. Blocks are inserted only if all predecessors are present (causal closure)
//! 3. Finalized blocks form an immutable prefix of the DAG
//! 4. The topological order is a valid linearization of the causal DAG
//!
//! Blocklace: a DAG-based data structure for Byzantine fault-tolerant consensus.
//!
//! This crate implements:
//! - Block creation and validation (content-addressed, hash-linked DAG)
//! - Cordial dissemination protocol (efficient gossip-based block propagation)
//!
//! ## Cordial Dissemination
//!
//! The key principle from the Cordial Miners paper: "send to others blocks you
//! know and think they need." Block pointers encode what each node knows,
//! enabling efficient catch-up without explicit protocol messages.
//!
//! ## Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────────┐
//! │  Blocklace (DAG of blocks with causal links)                        │
//! │     ↓                                                               │
//! │  Disseminator (cordial dissemination engine)                         │
//! │     ├── blocks_to_send(peer) → causally-closed delta                │
//! │     ├── received_from(peer, block) → update peer knowledge          │
//! │     └── handle_message(msg) → process Push/Pull/PullResponse        │
//! └─────────────────────────────────────────────────────────────────────┘
//! ```

pub mod addressing;
pub mod constitution;
pub mod cross_reference;
pub mod delegation;
pub mod dissemination;
pub mod dregg_bridge;
pub mod finality;
pub mod ordering;

use std::collections::{HashMap, HashSet, VecDeque};

use serde::{Deserialize, Serialize};

/// A block identifier: the BLAKE3 hash of the block's canonical encoding.
pub type BlockId = [u8; 32];

/// A node identifier: the public key (32 bytes) of the block creator.
pub type NodeKey = [u8; 32];

/// A block in the blocklace DAG.
///
/// Each block references its predecessors (causal dependencies) and is signed
/// by its creator. The block ID is the BLAKE3 hash of (creator || sequence ||
/// predecessors || payload).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Block {
    /// The creator's public key.
    pub creator: NodeKey,
    /// Monotonic sequence number for this creator (0-indexed).
    pub sequence: u64,
    /// Block IDs this block depends on (causal predecessors).
    pub predecessors: Vec<BlockId>,
    /// Application-level payload.
    pub payload: Vec<u8>,
    /// Signature over the block hash by the creator (64 bytes, Ed25519).
    /// Set to zeros for unsigned/test blocks.
    #[serde(with = "serde_sig64")]
    pub signature: [u8; 64],
}

/// Serde helper for 64-byte arrays (Ed25519 signatures).
/// Serde only implements Serialize/Deserialize for arrays up to [T; 32].
pub(crate) mod serde_sig64 {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S: Serializer>(bytes: &[u8; 64], serializer: S) -> Result<S::Ok, S::Error> {
        bytes.as_ref().serialize(serializer)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<[u8; 64], D::Error> {
        let v: Vec<u8> = Deserialize::deserialize(deserializer)?;
        v.try_into()
            .map_err(|_| serde::de::Error::custom("expected 64 bytes for signature"))
    }
}

impl Block {
    /// Compute the canonical block ID (BLAKE3 hash of the block's content).
    ///
    /// The hash covers: creator, sequence, predecessors (sorted), and payload.
    /// It does NOT cover the signature (so the signature can be verified against
    /// the hash without circular dependency).
    pub fn id(&self) -> BlockId {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-blocklace-block-v1");
        hasher.update(&self.creator);
        hasher.update(&self.sequence.to_le_bytes());
        hasher.update(&(self.predecessors.len() as u32).to_le_bytes());
        let mut sorted_preds = self.predecessors.clone();
        sorted_preds.sort();
        for pred in &sorted_preds {
            hasher.update(pred);
        }
        hasher.update(&(self.payload.len() as u32).to_le_bytes());
        hasher.update(&self.payload);
        *hasher.finalize().as_bytes()
    }

    /// Create a new unsigned block.
    pub fn new(
        creator: NodeKey,
        sequence: u64,
        predecessors: Vec<BlockId>,
        payload: Vec<u8>,
    ) -> Self {
        Self {
            creator,
            sequence,
            predecessors,
            payload,
            signature: [0u8; 64],
        }
    }

    /// Serialize the block to bytes for wire transmission.
    ///
    /// Uses postcard's compact binary format.
    pub fn to_bytes(&self) -> Vec<u8> {
        postcard::to_stdvec(self).expect("block serialization should not fail")
    }

    /// Deserialize a block from bytes.
    ///
    /// Returns `None` if the bytes are malformed.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        postcard::from_bytes(bytes).ok()
    }
}

/// The local blocklace: stores all known blocks and their relationships.
#[derive(Clone, Debug, Default)]
pub struct Blocklace {
    /// All blocks by their ID.
    pub(crate) blocks: HashMap<BlockId, Block>,
    /// Forward edges: block_id -> set of blocks that reference it as a predecessor.
    successors: HashMap<BlockId, HashSet<BlockId>>,
    /// The latest block ID per creator (tip of each creator's chain).
    tips: HashMap<NodeKey, BlockId>,
    /// Blocks with no successors (the current DAG frontier).
    frontier: HashSet<BlockId>,
}

impl Blocklace {
    /// Create a new empty blocklace.
    pub fn new() -> Self {
        Self::default()
    }

    /// Insert a block into the blocklace.
    ///
    /// Returns `Ok(block_id)` if the block was inserted (or already exists).
    /// Returns `Err` with the list of missing predecessor IDs if the block
    /// cannot be inserted because its causal dependencies are not present.
    pub fn insert(&mut self, block: Block) -> Result<BlockId, Vec<BlockId>> {
        let block_id = block.id();

        // Already have it.
        if self.blocks.contains_key(&block_id) {
            return Ok(block_id);
        }

        // Check all predecessors are present.
        let missing: Vec<BlockId> = block
            .predecessors
            .iter()
            .filter(|p| !self.blocks.contains_key(*p))
            .copied()
            .collect();
        if !missing.is_empty() {
            return Err(missing);
        }

        // Remove predecessors from the frontier (they now have a successor).
        for pred in &block.predecessors {
            self.frontier.remove(pred);
            self.successors.entry(*pred).or_default().insert(block_id);
        }

        // This block is on the frontier.
        self.frontier.insert(block_id);
        self.successors.entry(block_id).or_default();

        // Update the tip for this creator.
        self.tips.insert(block.creator, block_id);

        self.blocks.insert(block_id, block);

        Ok(block_id)
    }

    /// Check if a block exists in the blocklace.
    pub fn contains(&self, block_id: &BlockId) -> bool {
        self.blocks.contains_key(block_id)
    }

    /// Get a block by its ID.
    pub fn get(&self, block_id: &BlockId) -> Option<&Block> {
        self.blocks.get(block_id)
    }

    /// Get the current frontier (blocks with no successors).
    pub fn frontier(&self) -> &HashSet<BlockId> {
        &self.frontier
    }

    /// Get the tip (latest block) for a given creator.
    pub fn tip_for(&self, creator: &NodeKey) -> Option<&BlockId> {
        self.tips.get(creator)
    }

    /// Get all tips (latest block per creator).
    pub fn tips(&self) -> &HashMap<NodeKey, BlockId> {
        &self.tips
    }

    /// Number of blocks in the blocklace.
    pub fn len(&self) -> usize {
        self.blocks.len()
    }

    /// Whether the blocklace is empty.
    pub fn is_empty(&self) -> bool {
        self.blocks.is_empty()
    }

    /// Get all block IDs.
    pub fn block_ids(&self) -> HashSet<BlockId> {
        self.blocks.keys().copied().collect()
    }

    /// Get the causal past (all ancestors) of a block, inclusive of the block itself.
    pub fn causal_past(&self, block_id: &BlockId) -> HashSet<BlockId> {
        let mut result = HashSet::new();
        let mut queue = VecDeque::new();
        queue.push_back(*block_id);

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

    /// Return blocks in topological order (predecessors before dependents).
    pub fn topological_order(&self) -> Vec<BlockId> {
        let mut in_degree: HashMap<BlockId, usize> = HashMap::new();
        for (id, block) in &self.blocks {
            let pred_count = block
                .predecessors
                .iter()
                .filter(|p| self.blocks.contains_key(*p))
                .count();
            in_degree.insert(*id, pred_count);
        }

        let mut queue: VecDeque<BlockId> = VecDeque::new();
        let mut initial: Vec<BlockId> = in_degree
            .iter()
            .filter(|&(_, &deg)| deg == 0)
            .map(|(&id, _)| id)
            .collect();
        initial.sort();
        queue.extend(initial);

        let mut result = Vec::with_capacity(self.blocks.len());
        while let Some(block_id) = queue.pop_front() {
            result.push(block_id);
            if let Some(succs) = self.successors.get(&block_id) {
                let mut next: Vec<BlockId> = Vec::new();
                for succ in succs {
                    if let Some(deg) = in_degree.get_mut(succ) {
                        *deg -= 1;
                        if *deg == 0 {
                            next.push(*succ);
                        }
                    }
                }
                next.sort();
                queue.extend(next);
            }
        }

        result
    }

    /// Get blocks in topological order, filtered to only include the given set.
    pub fn topological_subset(&self, subset: &HashSet<BlockId>) -> Vec<BlockId> {
        self.topological_order()
            .into_iter()
            .filter(|id| subset.contains(id))
            .collect()
    }
}

#[cfg(test)]
mod finality_tests;

#[cfg(test)]
mod tests {
    use super::*;

    fn make_block(creator: u8, seq: u64, preds: Vec<BlockId>, payload: &[u8]) -> Block {
        Block::new([creator; 32], seq, preds, payload.to_vec())
    }

    #[test]
    fn block_id_deterministic() {
        let b = make_block(1, 0, vec![], b"hello");
        let id1 = b.id();
        let id2 = b.id();
        assert_eq!(id1, id2);
    }

    #[test]
    fn block_id_varies_on_content() {
        let b1 = make_block(1, 0, vec![], b"hello");
        let b2 = make_block(1, 0, vec![], b"world");
        assert_ne!(b1.id(), b2.id());
    }

    #[test]
    fn insert_genesis() {
        let mut lace = Blocklace::new();
        let b = make_block(1, 0, vec![], b"genesis");
        let id = lace.insert(b).unwrap();
        assert!(lace.contains(&id));
        assert_eq!(lace.len(), 1);
        assert!(lace.frontier().contains(&id));
    }

    #[test]
    fn insert_with_predecessor() {
        let mut lace = Blocklace::new();
        let b1 = make_block(1, 0, vec![], b"first");
        let id1 = lace.insert(b1).unwrap();

        let b2 = make_block(1, 1, vec![id1], b"second");
        let id2 = lace.insert(b2).unwrap();

        assert_eq!(lace.len(), 2);
        assert!(!lace.frontier().contains(&id1));
        assert!(lace.frontier().contains(&id2));
    }

    #[test]
    fn insert_missing_predecessor_fails() {
        let mut lace = Blocklace::new();
        let fake_pred = [0xAA; 32];
        let b = make_block(1, 0, vec![fake_pred], b"orphan");
        let err = lace.insert(b).unwrap_err();
        assert_eq!(err, vec![fake_pred]);
    }

    #[test]
    fn causal_past() {
        let mut lace = Blocklace::new();
        let b1 = make_block(1, 0, vec![], b"a");
        let id1 = lace.insert(b1).unwrap();
        let b2 = make_block(2, 0, vec![], b"b");
        let id2 = lace.insert(b2).unwrap();
        let b3 = make_block(1, 1, vec![id1, id2], b"c");
        let id3 = lace.insert(b3).unwrap();

        let past = lace.causal_past(&id3);
        assert!(past.contains(&id1));
        assert!(past.contains(&id2));
        assert!(past.contains(&id3));
        assert_eq!(past.len(), 3);
    }

    #[test]
    fn topological_order_respects_causality() {
        let mut lace = Blocklace::new();
        let b1 = make_block(1, 0, vec![], b"a");
        let id1 = lace.insert(b1).unwrap();
        let b2 = make_block(2, 0, vec![], b"b");
        let id2 = lace.insert(b2).unwrap();
        let b3 = make_block(1, 1, vec![id1, id2], b"c");
        let id3 = lace.insert(b3).unwrap();

        let order = lace.topological_order();
        let pos1 = order.iter().position(|x| *x == id1).unwrap();
        let pos2 = order.iter().position(|x| *x == id2).unwrap();
        let pos3 = order.iter().position(|x| *x == id3).unwrap();
        assert!(pos1 < pos3);
        assert!(pos2 < pos3);
    }

    #[test]
    fn tips_tracking() {
        let mut lace = Blocklace::new();
        let b1 = make_block(1, 0, vec![], b"a");
        let id1 = lace.insert(b1).unwrap();
        assert_eq!(*lace.tip_for(&[1; 32]).unwrap(), id1);

        let b2 = make_block(1, 1, vec![id1], b"b");
        let id2 = lace.insert(b2).unwrap();
        assert_eq!(*lace.tip_for(&[1; 32]).unwrap(), id2);
    }

    #[test]
    fn duplicate_insert_is_idempotent() {
        let mut lace = Blocklace::new();
        let b = make_block(1, 0, vec![], b"dup");
        let id1 = lace.insert(b.clone()).unwrap();
        let id2 = lace.insert(b).unwrap();
        assert_eq!(id1, id2);
        assert_eq!(lace.len(), 1);
    }
}
