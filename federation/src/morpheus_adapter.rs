//! Morpheus consensus adapter for the federation crate.
//!
//! The morpheus adapter provides full DAG-based BFT with BLS threshold signatures.
//! Without this feature (`morpheus`), the simplified round-robin consensus is used.
//!
//! This module bridges the morpheus protocol's message types and process lifecycle
//! into the federation's existing `ConsensusState` / `FederationTransport` interface.
//! It allows a federation node to use the morpheus consensus engine for block
//! finalization instead of the simplified single-round-per-block approach.
//!
//! # Usage
//!
//! ```ignore
//! use pyana_federation::morpheus_adapter::MorpheusAdapter;
//!
//! let adapter = MorpheusAdapter::new(config, node_id);
//! adapter.submit_event(revocation_event);
//!
//! // In the message processing loop:
//! adapter.handle_incoming(raw_bytes);
//! for block in adapter.take_finalized() {
//!     // apply to state
//! }
//! ```

use std::collections::{BTreeSet, VecDeque};

use pyana_morpheus::test_harness::TestTransaction;
use pyana_morpheus::{BlockData, BlockKey, Identity, KeyBook, Message, MorpheusProcess, ViewNum};

use crate::node::ConsensusConfig;
use crate::types::RevocationEvent;

/// Configuration for the Morpheus adapter.
#[derive(Clone, Debug)]
pub struct MorpheusAdapterConfig {
    /// The federation consensus config (node count, threshold, etc.)
    pub federation_config: ConsensusConfig,
    /// The node's index in the federation (0-based).
    pub node_id: usize,
    /// Network delay parameter (delta) in logical time units.
    pub delta: u128,
}

/// Wraps a `MorpheusProcess` to provide the federation with DAG-based BFT consensus.
///
/// The adapter translates between the federation's revocation-event-based interface
/// and the morpheus protocol's generic transaction block machinery.
pub struct MorpheusAdapter {
    /// The underlying morpheus process instance.
    process: MorpheusProcess<TestTransaction>,
    /// Outbound messages produced by the morpheus process, waiting to be sent
    /// via the federation transport layer.
    outbox: VecDeque<(Message<TestTransaction>, Option<Identity>)>,
    /// Blocks that morpheus has finalized but the federation layer has not yet consumed.
    finalized_blocks: VecDeque<FinalizedMorpheusBlock>,
    /// Pending revocation events to be included in the next transaction block.
    pending_events: Vec<RevocationEvent>,
    /// Adapter configuration.
    config: MorpheusAdapterConfig,
    /// Tracks which finalized block keys have already been extracted into `finalized_blocks`,
    /// so we only emit each finalized block once.
    seen_finalized: BTreeSet<BlockKey>,
}

/// A block finalized by the morpheus consensus engine, translated into federation terms.
#[derive(Clone, Debug)]
pub struct FinalizedMorpheusBlock {
    /// The view in which this block was finalized.
    pub view: i64,
    /// The height of the finalized block.
    pub height: usize,
    /// The revocation events contained in this block (if it was a transaction block).
    pub events: Vec<RevocationEvent>,
}

impl MorpheusAdapter {
    /// Create a new morpheus adapter for a federation node.
    ///
    /// # Arguments
    ///
    /// * `config` - Adapter configuration including node identity and federation params.
    /// * `keybook` - The BLS key material for the morpheus threshold signature scheme.
    pub fn new(config: MorpheusAdapterConfig, keybook: KeyBook) -> Self {
        let n = config.federation_config.num_nodes as u32;
        let f = config.federation_config.max_faults as u32;
        let id = Identity(config.node_id as u32 + 1); // morpheus uses 1-indexed identities

        let mut process = MorpheusProcess::new(keybook, id, n, f);
        process.delta = config.delta;

        // The genesis block is already in `index.finalized` at construction; seed
        // our tracking set so we don't emit it as a "new" finalized block.
        let seen_finalized = process.index.finalized.clone();

        MorpheusAdapter {
            process,
            outbox: VecDeque::new(),
            finalized_blocks: VecDeque::new(),
            pending_events: Vec::new(),
            config,
            seen_finalized,
        }
    }

    /// Submit a revocation event to be included in the next morpheus transaction block.
    pub fn submit_event(&mut self, event: RevocationEvent) {
        self.pending_events.push(event);
    }

    /// Advance the morpheus process's logical clock.
    pub fn set_time(&mut self, now: u128) {
        self.process.set_now(now);
    }

    /// Feed an incoming morpheus protocol message from the transport layer.
    ///
    /// Returns true if the message was processed successfully.
    pub fn handle_incoming(&mut self, message: Message<TestTransaction>, sender: Identity) -> bool {
        let mut to_send = Vec::new();
        let result = self.process.process_message(message, sender, &mut to_send);
        self.outbox.extend(to_send.into_iter());
        self.collect_newly_finalized();
        result
    }

    /// Check protocol timeouts and produce any necessary view-change messages.
    pub fn check_timeouts(&mut self) {
        let mut to_send = Vec::new();
        self.process.check_timeouts(&mut to_send);
        self.outbox.extend(to_send.into_iter());
        self.collect_newly_finalized();
    }

    /// Attempt to produce a new block if the process has pending transactions
    /// and the protocol state allows it.
    pub fn try_produce_block(&mut self) {
        // Convert pending revocation events into morpheus test transactions.
        // In a full integration, we'd define a proper Transaction type; for now
        // we serialize events into the TestTransaction payload.
        if !self.pending_events.is_empty() {
            for event in self.pending_events.drain(..) {
                let payload = postcard::to_stdvec(&event).unwrap_or_default();
                self.process
                    .ready_transactions
                    .push(TestTransaction(payload));
            }
        }

        let mut to_send = Vec::new();
        self.process.try_produce_blocks(&mut to_send);
        self.outbox.extend(to_send.into_iter());
        self.collect_newly_finalized();
    }

    /// Scan `process.index.finalized` for newly finalized block keys that have not
    /// yet been emitted, extract the corresponding block data, and push translated
    /// `FinalizedMorpheusBlock` entries into the output queue.
    fn collect_newly_finalized(&mut self) {
        // Identify block keys that are in the process's finalized set but not yet seen.
        let new_keys: Vec<BlockKey> = self
            .process
            .index
            .finalized
            .iter()
            .filter(|key| !self.seen_finalized.contains(key))
            .cloned()
            .collect();

        for key in new_keys {
            self.seen_finalized.insert(key.clone());

            // Extract transaction payloads from the block if it is a Tr block.
            let events = self
                .process
                .index
                .blocks
                .get(&key)
                .and_then(|signed_block| match &signed_block.data.data {
                    BlockData::Tr { transactions } => {
                        let evts: Vec<RevocationEvent> = transactions
                            .iter()
                            .filter_map(|tx| postcard::from_bytes(&tx.0).ok())
                            .collect();
                        Some(evts)
                    }
                    _ => None,
                })
                .unwrap_or_default();

            self.finalized_blocks.push_back(FinalizedMorpheusBlock {
                view: key.view.0,
                height: key.height,
                events,
            });
        }
    }

    /// Drain outbound messages that need to be sent via the federation transport.
    ///
    /// Each entry is (message, optional_target). If target is None, broadcast to all.
    pub fn drain_outbox(
        &mut self,
    ) -> impl Iterator<Item = (Message<TestTransaction>, Option<Identity>)> + '_ {
        self.outbox.drain(..)
    }

    /// Take all finalized blocks that have not yet been consumed by the federation layer.
    pub fn take_finalized(&mut self) -> Vec<FinalizedMorpheusBlock> {
        self.finalized_blocks.drain(..).collect()
    }

    /// Get a reference to the underlying morpheus process (for inspection/debugging).
    pub fn process(&self) -> &MorpheusProcess<TestTransaction> {
        &self.process
    }

    /// Get the current view of the morpheus process.
    pub fn current_view(&self) -> ViewNum {
        self.process.view_i
    }

    /// Get the number of finalized blocks tracked by the morpheus process.
    pub fn finalized_count(&self) -> usize {
        self.process.index.finalized.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_morpheus::test_harness::TestTransaction;
    use pyana_morpheus::{
        Block, BlockData, BlockHash, BlockType, GEN_BLOCK_KEY, Signed, SlotNum, ViewNum,
    };
    use std::sync::Arc;

    /// Helper: create a minimal adapter for testing.
    fn make_test_adapter() -> MorpheusAdapter {
        use pyana_morpheus::test_harness::SimulationHarness;
        let harness = SimulationHarness::create_test_setup(4);
        let process = harness.processes.values().next().unwrap().clone();
        let config = MorpheusAdapterConfig {
            federation_config: ConsensusConfig::new(4),
            node_id: 0,
            delta: 100,
        };
        let seen_finalized = process.index.finalized.clone();
        MorpheusAdapter {
            process,
            outbox: VecDeque::new(),
            finalized_blocks: VecDeque::new(),
            pending_events: Vec::new(),
            config,
            seen_finalized,
        }
    }

    #[test]
    fn test_collect_newly_finalized_emits_new_blocks() {
        let mut adapter = make_test_adapter();

        // Initially, take_finalized should return nothing (genesis is already in seen_finalized).
        assert!(adapter.take_finalized().is_empty());

        // Simulate a finalized block by inserting a BlockKey into process.index.finalized
        // and a corresponding block into process.index.blocks.
        let fake_key = BlockKey {
            type_: BlockType::Tr,
            view: ViewNum(0),
            height: 1,
            author: Some(Identity(1)),
            slot: SlotNum(0),
            hash: Some(BlockHash(42)),
        };

        // Create a Tr block containing a serialized revocation event.
        let event = RevocationEvent {
            token_id: "token-42".to_string(),
            authority_id: 0,
            signature: crate::types::Signature([1u8; 64]),
        };
        let payload = postcard::to_stdvec(&event).unwrap();
        let tx = TestTransaction(payload);

        let block = Block {
            key: fake_key.clone(),
            prev: vec![adapter.process.genesis_qc.clone()],
            one: adapter.process.genesis_qc.clone(),
            data: BlockData::Tr {
                transactions: vec![tx],
            },
        };
        let signed_block = Arc::new(Signed {
            data: block,
            author: Identity(1),
            signature: hints::PartialSignature::default(),
        });

        // Insert the block and mark it finalized in the morpheus index.
        adapter
            .process
            .index
            .blocks
            .insert(fake_key.clone(), signed_block);
        adapter.process.index.finalized.insert(fake_key.clone());

        // Trigger collect_newly_finalized by calling check_timeouts (which calls it).
        adapter.check_timeouts();

        // take_finalized should now return the newly finalized block.
        let finalized = adapter.take_finalized();
        assert_eq!(finalized.len(), 1);
        assert_eq!(finalized[0].view, 0);
        assert_eq!(finalized[0].height, 1);
        assert_eq!(finalized[0].events.len(), 1);
        assert_eq!(finalized[0].events[0].token_id, "token-42");

        // Calling again returns empty.
        assert!(adapter.take_finalized().is_empty());

        // Adding the same key again should not produce duplicates.
        adapter.check_timeouts();
        assert!(adapter.take_finalized().is_empty());
    }

    #[test]
    fn test_collect_newly_finalized_skips_genesis() {
        let adapter = make_test_adapter();
        // Genesis is in process.index.finalized but should NOT be emitted.
        assert!(adapter.finalized_blocks.is_empty());
    }

    #[test]
    fn test_collect_newly_finalized_leader_block_has_empty_events() {
        let mut adapter = make_test_adapter();

        let fake_key = BlockKey {
            type_: BlockType::Lead,
            view: ViewNum(0),
            height: 1,
            author: Some(Identity(1)),
            slot: SlotNum(0),
            hash: Some(BlockHash(99)),
        };

        let block = Block {
            key: fake_key.clone(),
            prev: vec![adapter.process.genesis_qc.clone()],
            one: adapter.process.genesis_qc.clone(),
            data: BlockData::Lead {
                justification: vec![],
            },
        };
        let signed_block = Arc::new(Signed {
            data: block,
            author: Identity(1),
            signature: hints::PartialSignature::default(),
        });

        adapter
            .process
            .index
            .blocks
            .insert(fake_key.clone(), signed_block);
        adapter.process.index.finalized.insert(fake_key.clone());

        adapter.check_timeouts();

        let finalized = adapter.take_finalized();
        assert_eq!(finalized.len(), 1);
        assert_eq!(finalized[0].height, 1);
        // Leader blocks have no transaction data, so events should be empty.
        assert!(finalized[0].events.is_empty());
    }
}
