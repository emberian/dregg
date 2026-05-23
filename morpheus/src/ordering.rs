//! Total ordering extraction (F/tau from Section 4 of the Morpheus paper).
//!
//! The Morpheus DAG-BFT protocol finalizes blocks, but the DAG structure means
//! multiple blocks may be finalized without an inherent linear order between them.
//! For State Machine Replication (SMR), we need a deterministic total order over
//! all finalized transactions that every honest node agrees upon.
//!
//! The ordering function F takes the set of finalized blocks and produces a linear
//! sequence of transactions by:
//! 1. Sorting finalized transaction blocks by (height, then BlockKey for ties)
//! 2. Within each block, yielding transactions in their block-internal position order
//! 3. Deduplicating: a transaction appearing in multiple blocks is only yielded once
//!    (at its first occurrence in the total order)
//!
//! The `OrderingCursor` provides monotonicity: once a transaction has been ordered
//! and yielded, it is never yielded again even as new blocks are finalized.

use std::collections::{BTreeSet, HashSet};
use std::sync::Arc;

use serde::{Deserialize, Serialize};

use crate::{BlockData, BlockKey, BlockType, StateIndex, Transaction};

/// A cursor that tracks which finalized blocks have already been processed for
/// total ordering. This ensures monotonicity: transactions are yielded exactly
/// once, and their position in the total order never changes.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct OrderingCursor {
    /// Block keys that have already been yielded by a prior call to
    /// `extract_new_transactions`. Transactions in these blocks will not be
    /// yielded again.
    pub executed_blocks: BTreeSet<BlockKey>,
}

impl OrderingCursor {
    /// Create a new cursor with the genesis block already marked as executed.
    pub fn new() -> Self {
        Self {
            executed_blocks: BTreeSet::from([crate::GEN_BLOCK_KEY]),
        }
    }

    /// Create a cursor from an existing set of executed block keys.
    pub fn from_executed(executed: BTreeSet<BlockKey>) -> Self {
        Self {
            executed_blocks: executed,
        }
    }
}

impl Default for OrderingCursor {
    fn default() -> Self {
        Self::new()
    }
}

/// Extract the totally-ordered sequence of transactions from ALL finalized blocks.
///
/// This is the F/tau function from Section 4 of the Morpheus paper. It produces
/// a deterministic total order on transactions that all honest nodes will agree upon.
///
/// Ordering rule:
/// - Only Tr (transaction) blocks contribute transactions
/// - Finalized Tr blocks are sorted by (height ASC, then full BlockKey for ties)
/// - Within each block, transactions are yielded in their block-internal order
/// - Deduplication: if the same transaction appears in multiple finalized Tr blocks,
///   only its first occurrence (in the total order) is included
///
/// This function returns ALL finalized transactions from genesis. For incremental
/// use (yielding only new transactions), use `extract_new_transactions` with an
/// `OrderingCursor`.
pub fn extract_total_order<Tx: Transaction>(state: &StateIndex<Tx>) -> Vec<Arc<Tx>> {
    let mut ordered_blocks: Vec<&BlockKey> = state
        .finalized
        .iter()
        .filter(|bk| bk.type_ == BlockType::Tr)
        .collect();

    // Sort by (height, then full BlockKey lexicographic order for deterministic tie-breaking).
    // BlockKey's derived Ord is (type_, view, height, author, slot, hash), but for total
    // ordering we want height-primary. We sort by height first, then by the full BlockKey
    // for ties at the same height.
    ordered_blocks.sort_by(|a, b| a.height.cmp(&b.height).then_with(|| a.cmp(b)));

    let mut seen_txs: HashSet<Arc<Tx>> = HashSet::new();
    let mut result: Vec<Arc<Tx>> = Vec::new();

    for block_key in ordered_blocks {
        if let Some(signed_block) = state.blocks.get(block_key) {
            if let BlockData::Tr { transactions } = &signed_block.data.data {
                for tx in transactions {
                    let tx_arc = Arc::new(tx.clone());
                    if seen_txs.insert(tx_arc.clone()) {
                        result.push(tx_arc);
                    }
                }
            }
        }
    }

    result
}

/// Extract only the NEW transactions that have been finalized since the cursor
/// was last advanced. This is the incremental version of `extract_total_order`
/// suitable for use in the consensus driver loop.
///
/// Returns the ordered transactions and advances the cursor so that subsequent
/// calls will not re-yield them.
///
/// The ordering is identical to `extract_total_order` restricted to blocks not
/// yet in the cursor's executed set. Because the ordering is height-primary and
/// heights are monotonically increasing for new finalizations, appending new
/// transactions to the existing sequence preserves the global total order.
///
/// Deduplication is performed against transactions in ALL finalized blocks
/// (including those already executed), ensuring a transaction that appears in
/// both an old and new block is never double-executed.
pub fn extract_new_transactions<Tx: Transaction>(
    state: &StateIndex<Tx>,
    cursor: &mut OrderingCursor,
) -> Vec<Tx> {
    // Identify newly finalized Tr blocks not yet in the cursor.
    let mut new_blocks: Vec<&BlockKey> = state
        .finalized
        .iter()
        .filter(|bk| bk.type_ == BlockType::Tr && !cursor.executed_blocks.contains(bk))
        .collect();

    if new_blocks.is_empty() {
        return Vec::new();
    }

    // Sort new blocks by (height, then full BlockKey for deterministic tie-breaking).
    new_blocks.sort_by(|a, b| a.height.cmp(&b.height).then_with(|| a.cmp(b)));

    // Build the deduplication set from ALL previously-executed blocks' transactions.
    // This ensures we never yield a transaction that was already executed in a prior block.
    let mut seen_txs: HashSet<Tx> = HashSet::new();
    for executed_bk in &cursor.executed_blocks {
        if executed_bk.type_ == BlockType::Tr {
            if let Some(signed_block) = state.blocks.get(executed_bk) {
                if let BlockData::Tr { transactions } = &signed_block.data.data {
                    for tx in transactions {
                        seen_txs.insert(tx.clone());
                    }
                }
            }
        }
    }

    // Yield new transactions in total order, deduplicating.
    let mut result: Vec<Tx> = Vec::new();
    for block_key in &new_blocks {
        if let Some(signed_block) = state.blocks.get(*block_key) {
            if let BlockData::Tr { transactions } = &signed_block.data.data {
                for tx in transactions {
                    if seen_txs.insert(tx.clone()) {
                        result.push(tx.clone());
                    }
                }
            }
        }
        // Mark this block as executed in the cursor.
        cursor.executed_blocks.insert((*block_key).clone());
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::crypto::*;
    use crate::types::*;
    use std::sync::Arc;

    /// A minimal transaction type for testing.
    #[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Serialize, Deserialize)]
    struct TestTx(u64);

    impl ark_serialize::CanonicalSerialize for TestTx {
        fn serialize_with_mode<W: std::io::Write>(
            &self,
            writer: W,
            compress: ark_serialize::Compress,
        ) -> Result<(), ark_serialize::SerializationError> {
            self.0.serialize_with_mode(writer, compress)
        }
        fn serialized_size(&self, _compress: ark_serialize::Compress) -> usize {
            8
        }
    }

    impl ark_serialize::Valid for TestTx {
        fn check(&self) -> Result<(), ark_serialize::SerializationError> {
            Ok(())
        }
    }

    impl ark_serialize::CanonicalDeserialize for TestTx {
        fn deserialize_with_mode<R: std::io::Read>(
            reader: R,
            compress: ark_serialize::Compress,
            validate: ark_serialize::Validate,
        ) -> Result<Self, ark_serialize::SerializationError> {
            Ok(TestTx(u64::deserialize_with_mode(
                reader, compress, validate,
            )?))
        }
    }

    impl Transaction for TestTx {}

    fn make_block_key(height: usize, view: i64, slot: u64) -> BlockKey {
        BlockKey {
            type_: BlockType::Tr,
            view: ViewNum(view),
            height,
            author: Some(Identity(1)),
            slot: SlotNum(slot),
            hash: Some(BlockHash(slot * 1000 + height as u64)),
        }
    }

    fn make_genesis_qc() -> FinishedQC {
        Arc::new(ThreshSigned {
            data: VoteData {
                z: 1,
                for_which: GEN_BLOCK_KEY,
            },
            signature: hints::Signature::default(),
        })
    }

    fn make_signed_block(key: BlockKey, txs: Vec<TestTx>) -> Arc<Signed<Block<TestTx>>> {
        Arc::new(Signed {
            data: Block {
                key: key.clone(),
                prev: vec![make_genesis_qc()],
                one: make_genesis_qc(),
                data: BlockData::Tr { transactions: txs },
            },
            author: Identity(1),
            signature: hints::PartialSignature::default(),
        })
    }

    #[test]
    fn test_extract_total_order_empty() {
        let genesis_qc = make_genesis_qc();
        let genesis_block = Arc::new(Signed {
            data: Block {
                key: GEN_BLOCK_KEY,
                prev: Vec::new(),
                one: genesis_qc.clone(),
                data: BlockData::Genesis,
            },
            author: Identity(u32::MAX),
            signature: hints::PartialSignature::default(),
        });
        let state: StateIndex<TestTx> = StateIndex::new(genesis_qc, genesis_block);
        let result = extract_total_order(&state);
        assert!(result.is_empty());
    }

    #[test]
    fn test_extract_total_order_single_block() {
        let genesis_qc = make_genesis_qc();
        let genesis_block = Arc::new(Signed {
            data: Block {
                key: GEN_BLOCK_KEY,
                prev: Vec::new(),
                one: genesis_qc.clone(),
                data: BlockData::Genesis,
            },
            author: Identity(u32::MAX),
            signature: hints::PartialSignature::default(),
        });
        let mut state: StateIndex<TestTx> = StateIndex::new(genesis_qc, genesis_block);

        let bk = make_block_key(1, 0, 0);
        let block = make_signed_block(bk.clone(), vec![TestTx(1), TestTx(2), TestTx(3)]);
        state.blocks.insert(bk.clone(), block);
        state.finalized.insert(bk);

        let result = extract_total_order(&state);
        assert_eq!(result.len(), 3);
        assert_eq!(*result[0], TestTx(1));
        assert_eq!(*result[1], TestTx(2));
        assert_eq!(*result[2], TestTx(3));
    }

    #[test]
    fn test_extract_total_order_height_ordering() {
        let genesis_qc = make_genesis_qc();
        let genesis_block = Arc::new(Signed {
            data: Block {
                key: GEN_BLOCK_KEY,
                prev: Vec::new(),
                one: genesis_qc.clone(),
                data: BlockData::Genesis,
            },
            author: Identity(u32::MAX),
            signature: hints::PartialSignature::default(),
        });
        let mut state: StateIndex<TestTx> = StateIndex::new(genesis_qc, genesis_block);

        // Insert blocks at different heights (out of order).
        let bk3 = make_block_key(3, 2, 2);
        let bk1 = make_block_key(1, 0, 0);
        let bk2 = make_block_key(2, 1, 1);

        state.blocks.insert(
            bk3.clone(),
            make_signed_block(bk3.clone(), vec![TestTx(30)]),
        );
        state.blocks.insert(
            bk1.clone(),
            make_signed_block(bk1.clone(), vec![TestTx(10)]),
        );
        state.blocks.insert(
            bk2.clone(),
            make_signed_block(bk2.clone(), vec![TestTx(20)]),
        );

        state.finalized.insert(bk3);
        state.finalized.insert(bk1);
        state.finalized.insert(bk2);

        let result = extract_total_order(&state);
        assert_eq!(result.len(), 3);
        // Should be ordered by height: 1, 2, 3
        assert_eq!(*result[0], TestTx(10));
        assert_eq!(*result[1], TestTx(20));
        assert_eq!(*result[2], TestTx(30));
    }

    #[test]
    fn test_extract_total_order_deduplication() {
        let genesis_qc = make_genesis_qc();
        let genesis_block = Arc::new(Signed {
            data: Block {
                key: GEN_BLOCK_KEY,
                prev: Vec::new(),
                one: genesis_qc.clone(),
                data: BlockData::Genesis,
            },
            author: Identity(u32::MAX),
            signature: hints::PartialSignature::default(),
        });
        let mut state: StateIndex<TestTx> = StateIndex::new(genesis_qc, genesis_block);

        // Two blocks at height 1 (from different authors), both containing TestTx(42).
        let bk1 = BlockKey {
            type_: BlockType::Tr,
            view: ViewNum(0),
            height: 1,
            author: Some(Identity(1)),
            slot: SlotNum(0),
            hash: Some(BlockHash(100)),
        };
        let bk2 = BlockKey {
            type_: BlockType::Tr,
            view: ViewNum(0),
            height: 1,
            author: Some(Identity(2)),
            slot: SlotNum(0),
            hash: Some(BlockHash(200)),
        };

        state.blocks.insert(
            bk1.clone(),
            make_signed_block(bk1.clone(), vec![TestTx(42), TestTx(1)]),
        );
        state.blocks.insert(
            bk2.clone(),
            make_signed_block(bk2.clone(), vec![TestTx(42), TestTx(2)]),
        );
        state.finalized.insert(bk1);
        state.finalized.insert(bk2);

        let result = extract_total_order(&state);
        // TestTx(42) should appear only once (from bk1, which sorts first by author).
        assert_eq!(result.len(), 3);
        assert_eq!(*result[0], TestTx(42));
        assert_eq!(*result[1], TestTx(1));
        assert_eq!(*result[2], TestTx(2));
    }

    #[test]
    fn test_extract_new_transactions_incremental() {
        let genesis_qc = make_genesis_qc();
        let genesis_block = Arc::new(Signed {
            data: Block {
                key: GEN_BLOCK_KEY,
                prev: Vec::new(),
                one: genesis_qc.clone(),
                data: BlockData::Genesis,
            },
            author: Identity(u32::MAX),
            signature: hints::PartialSignature::default(),
        });
        let mut state: StateIndex<TestTx> = StateIndex::new(genesis_qc, genesis_block);
        let mut cursor = OrderingCursor::new();

        // First batch: one block finalized.
        let bk1 = make_block_key(1, 0, 0);
        state.blocks.insert(
            bk1.clone(),
            make_signed_block(bk1.clone(), vec![TestTx(1), TestTx(2)]),
        );
        state.finalized.insert(bk1.clone());

        let batch1 = extract_new_transactions(&state, &mut cursor);
        assert_eq!(batch1, vec![TestTx(1), TestTx(2)]);

        // Second call with no new blocks: should be empty.
        let batch2 = extract_new_transactions(&state, &mut cursor);
        assert!(batch2.is_empty());

        // Third batch: new block finalized, with a duplicate tx.
        let bk2 = make_block_key(2, 1, 1);
        state.blocks.insert(
            bk2.clone(),
            make_signed_block(bk2.clone(), vec![TestTx(2), TestTx(3)]),
        );
        state.finalized.insert(bk2.clone());

        let batch3 = extract_new_transactions(&state, &mut cursor);
        // TestTx(2) already executed, only TestTx(3) is new.
        assert_eq!(batch3, vec![TestTx(3)]);
    }

    #[test]
    fn test_leader_blocks_excluded() {
        let genesis_qc = make_genesis_qc();
        let genesis_block = Arc::new(Signed {
            data: Block {
                key: GEN_BLOCK_KEY,
                prev: Vec::new(),
                one: genesis_qc.clone(),
                data: BlockData::Genesis,
            },
            author: Identity(u32::MAX),
            signature: hints::PartialSignature::default(),
        });
        let mut state: StateIndex<TestTx> = StateIndex::new(genesis_qc, genesis_block);

        // A finalized leader block should not contribute transactions.
        let lead_bk = BlockKey {
            type_: BlockType::Lead,
            view: ViewNum(0),
            height: 1,
            author: Some(Identity(1)),
            slot: SlotNum(0),
            hash: Some(BlockHash(999)),
        };
        state.finalized.insert(lead_bk);

        // A finalized Tr block.
        let tr_bk = make_block_key(1, 0, 0);
        state.blocks.insert(
            tr_bk.clone(),
            make_signed_block(tr_bk.clone(), vec![TestTx(7)]),
        );
        state.finalized.insert(tr_bk);

        let result = extract_total_order(&state);
        assert_eq!(result.len(), 1);
        assert_eq!(*result[0], TestTx(7));
    }
}
