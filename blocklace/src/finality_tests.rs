//! Tests for the blocklace data structure.

use std::collections::HashSet;

use ed25519_dalek::SigningKey;
use rand::rngs::OsRng;

use crate::dregg_bridge::{CodManager, DreggBlocklaceBridge, ExecutionTier, classify_turn};
use crate::finality::{Block, BlockError, Blocklace, FinalityLevel, FinalityTracker, Payload};

fn random_key() -> SigningKey {
    SigningKey::generate(&mut OsRng)
}

// ─── Signature Verification ──────────────────────────────────────────────────

#[test]
fn create_block_and_verify_signature() {
    let key = random_key();
    let mut lace = Blocklace::new_simple(key);
    let block = lace.add_block(Payload::Data(b"hello".to_vec()));
    assert_eq!(block.seq, 1);
    assert!(block.verify_signature().is_ok());
}

#[test]
fn tampered_block_fails_verification() {
    let key = random_key();
    let mut lace = Blocklace::new_simple(key);
    let mut block = lace.add_block(Payload::Data(b"hello".to_vec()));
    // Tamper with the payload.
    block.payload = Payload::Data(b"tampered".to_vec());
    assert!(block.verify_signature().is_err());
}

// ─── Virtual Chain ───────────────────────────────────────────────────────────

#[test]
fn virtual_chain_is_ordered() {
    let key = random_key();
    let mut lace = Blocklace::new_simple(key);
    let creator = lace.self_creator();

    lace.add_block(Payload::Data(b"a".to_vec()));
    lace.add_block(Payload::Data(b"b".to_vec()));
    lace.add_block(Payload::Data(b"c".to_vec()));

    let chain = lace.virtual_chain(&creator);
    assert_eq!(chain.len(), 3);
    assert_eq!(chain[0].seq, 1);
    assert_eq!(chain[1].seq, 2);
    assert_eq!(chain[2].seq, 3);
}

// ─── Merge ───────────────────────────────────────────────────────────────────

#[test]
fn merge_two_independent_blocklaces() {
    let key_a = random_key();
    let key_b = random_key();
    let creator_a = key_a.verifying_key().to_bytes();
    let creator_b = key_b.verifying_key().to_bytes();

    let mut lace_a = Blocklace::new_simple(key_a);
    let mut lace_b = Blocklace::new_simple(key_b);

    lace_a.add_block(Payload::Data(b"from A".to_vec()));
    lace_a.add_block(Payload::Data(b"from A2".to_vec()));
    lace_b.add_block(Payload::Data(b"from B".to_vec()));

    // Merge B's blocks into A.
    let delta = lace_b.all_blocks();
    lace_a.merge(delta).unwrap();

    assert_eq!(lace_a.len(), 3);
    assert_eq!(lace_a.virtual_chain(&creator_a).len(), 2);
    assert_eq!(lace_a.virtual_chain(&creator_b).len(), 1);
}

// ─── Equivocation Detection ──────────────────────────────────────────────────

#[test]
fn detect_equivocation_same_seq() {
    let key = random_key();
    let creator = key.verifying_key().to_bytes();

    // Create two blocks with same seq but different content.
    let block_a = Block::new(&key, 1, Payload::Data(b"version A".to_vec()), vec![]);
    let block_b = Block::new(&key, 1, Payload::Data(b"version B".to_vec()), vec![]);

    let mut lace = Blocklace::new_simple(random_key());

    // Insert block_a directly.
    lace.receive_block(block_a.clone()).unwrap();

    // Receiving block_b should detect equivocation.
    let result = lace.receive_block(block_b.clone());
    assert!(result.is_err());
    match result.unwrap_err() {
        BlockError::Equivocation { creator: c, .. } => {
            assert_eq!(c, creator);
        }
        other => panic!("expected equivocation, got: {other:?}"),
    }

    assert!(lace.equivocators().contains(&creator));
}

// ─── Closure Enforcement ─────────────────────────────────────────────────────

#[test]
fn closure_enforcement() {
    let key = random_key();
    use crate::finality::BlockId;

    // Create a block that references a non-existent predecessor.
    let fake_pred = BlockId([0xAB; 32]);
    let block = Block::new(&key, 1, Payload::Ack, vec![fake_pred]);

    let mut lace = Blocklace::new_simple(random_key());
    let result = lace.receive_block(block);
    assert!(matches!(result, Err(BlockError::MissingPredecessor { .. })));
}

// ─── Causal Past ─────────────────────────────────────────────────────────────

#[test]
fn causal_past_computation() {
    let key = random_key();
    let mut lace = Blocklace::new_simple(key);

    let b1 = lace.add_block(Payload::Data(b"1".to_vec()));
    let b1_id = b1.id();
    let b2 = lace.add_block(Payload::Data(b"2".to_vec()));
    let b2_id = b2.id();
    let b3 = lace.add_block(Payload::Data(b"3".to_vec()));
    let b3_id = b3.id();

    // b3's causal past should include b2 and b1.
    let past = lace.causal_past(&b3_id);
    assert!(past.contains(&b2_id));
    assert!(past.contains(&b1_id));

    // b1's causal past should be empty.
    let past_b1 = lace.causal_past(&b1_id);
    assert!(past_b1.is_empty());
}

#[test]
fn is_predecessor_relation() {
    let key = random_key();
    let mut lace = Blocklace::new_simple(key);

    let b1 = lace.add_block(Payload::Data(b"1".to_vec()));
    let b1_id = b1.id();
    let b2 = lace.add_block(Payload::Data(b"2".to_vec()));
    let b2_id = b2.id();

    assert!(lace.is_predecessor(&b1_id, &b2_id));
    assert!(!lace.is_predecessor(&b2_id, &b1_id));
    assert!(!lace.is_predecessor(&b1_id, &b1_id));
}

// ─── Frontier ────────────────────────────────────────────────────────────────

#[test]
fn frontier_computation() {
    let key = random_key();
    let mut lace = Blocklace::new_simple(key);

    let _b1 = lace.add_block(Payload::Data(b"1".to_vec()));
    let _b2 = lace.add_block(Payload::Data(b"2".to_vec()));
    let b3 = lace.add_block(Payload::Data(b"3".to_vec()));

    // Only b3 should be in the frontier.
    let frontier = lace.frontier();
    assert_eq!(frontier.len(), 1);
    assert_eq!(frontier[0], b3.id());
}

#[test]
fn frontier_with_multiple_creators() {
    let key_a = random_key();
    let key_b = random_key();

    let mut lace = Blocklace::new_simple(key_a);

    // A creates a block.
    let _a1 = lace.add_block(Payload::Data(b"A1".to_vec()));

    // B creates an independent block (no predecessors in common).
    let b_block = Block::new(&key_b, 1, Payload::Data(b"B1".to_vec()), vec![]);
    lace.receive_block(b_block.clone()).unwrap();

    // Frontier should have both A's tip and B's block.
    let frontier = lace.frontier();
    assert_eq!(frontier.len(), 2);
}

// ─── CRDT Properties ─────────────────────────────────────────────────────────

#[test]
fn crdt_associativity() {
    let key_a = random_key();
    let key_b = random_key();
    let key_c = random_key();

    let mut source_a = Blocklace::new_simple(key_a.clone());
    let mut source_b = Blocklace::new_simple(key_b.clone());
    let mut source_c = Blocklace::new_simple(key_c.clone());

    source_a.add_block(Payload::Data(b"A1".to_vec()));
    source_b.add_block(Payload::Data(b"B1".to_vec()));
    source_c.add_block(Payload::Data(b"C1".to_vec()));

    let delta_a = source_a.all_blocks();
    let delta_b = source_b.all_blocks();
    let delta_c = source_c.all_blocks();

    // merge(A, merge(B, C))
    let mut lace_1 = Blocklace::new_simple(random_key());
    lace_1.merge(delta_b.clone()).unwrap();
    lace_1.merge(delta_c.clone()).unwrap();
    lace_1.merge(delta_a.clone()).unwrap();

    // merge(merge(A, B), C)
    let mut lace_2 = Blocklace::new_simple(random_key());
    lace_2.merge(delta_a.clone()).unwrap();
    lace_2.merge(delta_b.clone()).unwrap();
    lace_2.merge(delta_c.clone()).unwrap();

    // Both should have the same set of blocks.
    assert_eq!(lace_1.len(), lace_2.len());
    for (id, _) in lace_1.iter() {
        assert!(lace_2.contains(id));
    }
}

#[test]
fn crdt_idempotent() {
    let key = random_key();
    let mut source = Blocklace::new_simple(key);
    source.add_block(Payload::Data(b"x".to_vec()));

    let delta = source.all_blocks();

    let mut target = Blocklace::new_simple(random_key());
    target.merge(delta.clone()).unwrap();
    let len_after_first = target.len();

    // Merging again should not change anything.
    target.merge(delta).unwrap();
    assert_eq!(target.len(), len_after_first);
}

#[test]
fn crdt_commutative() {
    let key_a = random_key();
    let key_b = random_key();

    let mut source_a = Blocklace::new_simple(key_a);
    let mut source_b = Blocklace::new_simple(key_b);

    source_a.add_block(Payload::Data(b"A".to_vec()));
    source_b.add_block(Payload::Data(b"B".to_vec()));

    let delta_a = source_a.all_blocks();
    let delta_b = source_b.all_blocks();

    // A then B
    let mut lace_1 = Blocklace::new_simple(random_key());
    lace_1.merge(delta_a.clone()).unwrap();
    lace_1.merge(delta_b.clone()).unwrap();

    // B then A
    let mut lace_2 = Blocklace::new_simple(random_key());
    lace_2.merge(delta_b).unwrap();
    lace_2.merge(delta_a).unwrap();

    assert_eq!(lace_1.len(), lace_2.len());
    for (id, _) in lace_1.iter() {
        assert!(lace_2.contains(id));
    }
}

// ─── Large Scale ─────────────────────────────────────────────────────────────

#[test]
fn large_scale_merge() {
    let num_creators = 100;
    let blocks_per_creator = 10;

    let keys: Vec<SigningKey> = (0..num_creators).map(|_| random_key()).collect();
    let mut sources: Vec<Blocklace> = keys
        .iter()
        .map(|k| Blocklace::new_simple(k.clone()))
        .collect();

    // Each creator produces their blocks.
    for source in &mut sources {
        for i in 0..blocks_per_creator {
            source.add_block(Payload::Data(format!("block {i}").into_bytes()));
        }
    }

    // Merge all into one target.
    let mut target = Blocklace::new_simple(random_key());
    for source in &sources {
        let delta = source.all_blocks();
        target.merge(delta).unwrap();
    }

    assert_eq!(target.len(), num_creators * blocks_per_creator);

    // Each creator's virtual chain should be totally ordered.
    for key in &keys {
        let creator = key.verifying_key().to_bytes();
        let chain = target.virtual_chain(&creator);
        assert_eq!(chain.len(), blocks_per_creator);
        for (i, block) in chain.iter().enumerate() {
            assert_eq!(block.seq, (i + 1) as u64);
        }
    }
}

// ─── Approval ────────────────────────────────────────────────────────────────

#[test]
fn approved_by_without_equivocation() {
    let key_a = random_key();
    let key_b = random_key();

    let mut lace = Blocklace::new_simple(key_a.clone());

    // B creates a block.
    let b_block = Block::new(&key_b, 1, Payload::Data(b"from B".to_vec()), vec![]);
    let b_id = b_block.id();
    lace.receive_block(b_block).unwrap();

    // A creates a block that sees B's block (through tips).
    let a_block = lace.add_block(Payload::Ack);
    let a_id = a_block.id();

    // A's block should approve B's block.
    assert!(lace.approved_by(&a_id, &b_id));
}

// ─── Delta For Peer ──────────────────────────────────────────────────────────

#[test]
fn delta_for_peer() {
    let key = random_key();
    let mut lace = Blocklace::new_simple(key);

    let b1 = lace.add_block(Payload::Data(b"1".to_vec()));
    let b1_id = b1.id();
    let _b2 = lace.add_block(Payload::Data(b"2".to_vec()));

    // Peer knows only b1.
    let known: HashSet<_> = [b1_id].into();
    let delta = lace.delta_for(&known);
    assert_eq!(delta.len(), 1);
    assert_eq!(delta[0].seq, 2);
}

// ─── Bridge Tests ────────────────────────────────────────────────────────────

#[test]
fn classify_turn_tiers() {
    let cod = CodManager::new(5);

    // Sovereign marker.
    let sovereign_turn = vec![0x01, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    assert_eq!(
        classify_turn(&sovereign_turn, &cod),
        ExecutionTier::Sovereign
    );

    // Optimistic marker (with budget).
    let optimistic_turn = vec![0x02, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    assert_eq!(
        classify_turn(&optimistic_turn, &cod),
        ExecutionTier::Optimistic
    );

    // Unknown marker -> Ordered.
    let ordered_turn = vec![0xFF, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    assert_eq!(classify_turn(&ordered_turn, &cod), ExecutionTier::Ordered);

    // Too short -> Ordered.
    let short_turn = vec![0x01, 0x02];
    assert_eq!(classify_turn(&short_turn, &cod), ExecutionTier::Ordered);
}

#[test]
fn cod_budget_management() {
    let mut cod = CodManager::new(2);
    let cell = [0x42; 32];

    assert!(cod.has_budget_for(&cell));
    cod.consume(&cell);
    assert!(cod.has_budget_for(&cell));
    cod.consume(&cell);
    assert!(!cod.has_budget_for(&cell)); // Budget exhausted.
    cod.release(&cell);
    assert!(cod.has_budget_for(&cell)); // Budget restored.
}

#[test]
fn bridge_submit_and_process() {
    let key = random_key();
    let mut lace = Blocklace::new(key, 3);
    let bridge = DreggBlocklaceBridge::new(5);

    let block_id = bridge.submit_turn(&mut lace, vec![0x01, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    assert!(lace.contains(&block_id));
    assert_eq!(lace.len(), 1);
}

// ─── Merge with causal closure failure ───────────────────────────────────────

#[test]
fn merge_not_causally_closed() {
    use crate::finality::{BlockId, MergeError};

    let key = random_key();
    // Create a block that references a non-existent predecessor.
    let fake_pred = BlockId([0xDE; 32]);
    let block = Block::new(&key, 1, Payload::Data(b"orphan".to_vec()), vec![fake_pred]);

    let mut target = Blocklace::new_simple(random_key());
    let result = target.merge(vec![block]);
    assert!(matches!(result, Err(MergeError::NotCausallyClosed { .. })));
}

// ─── Finality Level Ordering ────────────────────────────────────────────────

#[test]
fn finality_level_ordering_is_monotone() {
    // Verify the partial order: Local < Bilateral < Attested < Ordered
    assert!(FinalityLevel::Local < FinalityLevel::Bilateral);
    assert!(FinalityLevel::Bilateral < FinalityLevel::Attested);
    assert!(FinalityLevel::Attested < FinalityLevel::Ordered);
}

#[test]
fn finality_never_regresses() {
    let mut tracker = FinalityTracker::new(3); // quorum = 3
    let block_id = crate::finality::BlockId([0x42; 32]);

    // Start at Local.
    assert_eq!(tracker.finality_of(&block_id), FinalityLevel::Local);

    // First ack -> Bilateral.
    let level = tracker.record_ack(block_id, [1; 32]);
    assert_eq!(level, FinalityLevel::Bilateral);
    assert_eq!(tracker.finality_of(&block_id), FinalityLevel::Bilateral);

    // Second ack -> still Bilateral (not yet quorum).
    let level = tracker.record_ack(block_id, [2; 32]);
    assert_eq!(level, FinalityLevel::Bilateral);

    // Third ack -> Attested (quorum reached).
    let level = tracker.record_ack(block_id, [3; 32]);
    assert_eq!(level, FinalityLevel::Attested);
    assert_eq!(tracker.finality_of(&block_id), FinalityLevel::Attested);

    // Mark as ordered -> Ordered (strongest level).
    tracker.mark_ordered(block_id);
    assert_eq!(tracker.finality_of(&block_id), FinalityLevel::Ordered);

    // Additional acks don't regress it.
    tracker.record_ack(block_id, [4; 32]);
    assert_eq!(tracker.finality_of(&block_id), FinalityLevel::Ordered);
}

// ─── Remove Equivocator ─────────────────────────────────────────────────────

#[test]
fn remove_equivocator_excludes_from_tips() {
    let key_a = random_key();
    let key_b = random_key();
    let creator_b = key_b.verifying_key().to_bytes();

    let mut lace = Blocklace::new_simple(key_a);

    // Receive a block from B.
    let b_block = Block::new(&key_b, 1, Payload::Data(b"from B".to_vec()), vec![]);
    lace.receive_block(b_block).unwrap();

    // B should be in tips.
    assert!(lace.tips().contains_key(&creator_b));

    // Remove B as equivocator.
    assert!(lace.remove_equivocator(&creator_b));

    // B should no longer be in tips.
    assert!(!lace.tips().contains_key(&creator_b));

    // B is in equivocators set.
    assert!(lace.is_equivocator(&creator_b));

    // Removing again returns false (already known).
    assert!(!lace.remove_equivocator(&creator_b));
}

#[test]
fn equivocator_blocks_dont_update_tips() {
    let key_a = random_key();
    let key_b = random_key();
    let creator_b = key_b.verifying_key().to_bytes();

    let mut lace = Blocklace::new_simple(key_a);

    // B equivocates: two blocks at seq 1.
    let b1 = Block::new(&key_b, 1, Payload::Data(b"first".to_vec()), vec![]);
    let b2 = Block::new(&key_b, 1, Payload::Data(b"second".to_vec()), vec![]);

    lace.receive_block(b1).unwrap();
    let err = lace.receive_block(b2);
    assert!(err.is_err()); // equivocation detected

    // B should be marked as equivocator and NOT in tips.
    assert!(lace.is_equivocator(&creator_b));
    assert!(!lace.tips().contains_key(&creator_b));

    // Further blocks from B should not update tips.
    let b3 = Block::new(
        &key_b,
        2,
        Payload::Data(b"after equivocation".to_vec()),
        vec![],
    );
    // This will succeed since there's no matching seq=2 yet and it has no predecessors.
    let _ = lace.receive_block(b3);
    assert!(!lace.tips().contains_key(&creator_b));
}

// ─── Serialization Roundtrip ────────────────────────────────────────────────

#[test]
fn block_serialization_roundtrip() {
    let key = random_key();
    let block = Block::new(&key, 42, Payload::Data(b"payload data".to_vec()), vec![]);
    let id_before = block.id();

    let bytes = block.to_bytes();
    let restored = Block::from_bytes(&bytes).unwrap();

    assert_eq!(restored.id(), id_before);
    assert_eq!(restored.creator, block.creator);
    assert_eq!(restored.seq, block.seq);
    assert_eq!(restored.payload, block.payload);
    assert_eq!(restored.signature, block.signature);
    assert!(restored.verify_signature().is_ok());
}

#[test]
fn block_from_invalid_bytes_returns_none() {
    let garbage = vec![0xFF, 0xFE, 0xFD, 0xFC];
    assert!(Block::from_bytes(&garbage).is_none());
}

// ─── Checkpoint ─────────────────────────────────────────────────────────────

#[test]
fn checkpoint_and_restore() {
    let key = random_key();
    let mut lace = Blocklace::new(key.clone(), 3);

    // Add some blocks.
    let b1 = lace.add_block(Payload::Data(b"one".to_vec()));
    let b1_id = b1.id();
    let b2 = lace.add_block(Payload::Data(b"two".to_vec()));
    let b2_id = b2.id();
    let _b3 = lace.add_block(Payload::Data(b"three".to_vec()));

    // Mark one as ordered.
    lace.finality.mark_ordered(b1_id);

    // Take a checkpoint.
    let checkpoint = lace.checkpoint();

    // Restore from checkpoint.
    let restored = Blocklace::from_checkpoint(&checkpoint, key, 3).unwrap();

    // Verify state matches.
    assert_eq!(restored.len(), lace.len());
    assert!(restored.contains(&b1_id));
    assert!(restored.contains(&b2_id));
    assert_eq!(restored.finality.ordered_sequence().len(), 1);
    assert_eq!(restored.finality.ordered_sequence()[0], b1_id);
}

// ─── Metrics ────────────────────────────────────────────────────────────────

#[test]
fn metrics_reflect_state() {
    let key = random_key();
    let mut lace = Blocklace::new(key, 3);

    let metrics = lace.metrics();
    assert_eq!(metrics.block_count, 0);
    assert_eq!(metrics.equivocator_count, 0);
    assert_eq!(metrics.finality_lag, 0);

    // Add blocks.
    let b1 = lace.add_block(Payload::Data(b"one".to_vec()));
    let b1_id = b1.id();
    lace.add_block(Payload::Data(b"two".to_vec()));
    lace.add_block(Payload::Data(b"three".to_vec()));

    let metrics = lace.metrics();
    assert_eq!(metrics.block_count, 3);
    assert_eq!(metrics.finality_lag, 3); // 3 blocks, none ordered

    // Order one block.
    lace.finality.mark_ordered(b1_id);

    let metrics = lace.metrics();
    assert_eq!(metrics.ordered_count, 1);
    assert_eq!(metrics.finality_lag, 2); // 3 total - 1 ordered = 2
}

// ─── Process Finalized Idempotency ─────────────────────────────────────────

#[test]
fn process_finalized_no_duplicates() {
    let key = random_key();
    let mut lace = Blocklace::new(key, 3);
    let mut bridge = DreggBlocklaceBridge::new(5);

    // Submit turns.
    let turn_data = vec![0x01, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    let id1 = bridge.submit_turn(&mut lace, turn_data.clone());
    let id2 = bridge.submit_turn(&mut lace, turn_data.clone());

    // Mark both as ordered.
    lace.finality.mark_ordered(id1);
    lace.finality.mark_ordered(id2);

    // First call: should produce 2 receipts.
    let receipts = bridge.process_finalized(&lace);
    assert_eq!(receipts.len(), 2);
    assert_eq!(receipts[0].finality_height, 1);
    assert_eq!(receipts[1].finality_height, 2);

    // Second call: should produce 0 receipts (already processed).
    let receipts = bridge.process_finalized(&lace);
    assert_eq!(receipts.len(), 0);

    // Add a third turn and order it.
    let id3 = bridge.submit_turn(&mut lace, turn_data);
    lace.finality.mark_ordered(id3);

    // Third call: should produce exactly 1 receipt (only the new one).
    let receipts = bridge.process_finalized(&lace);
    assert_eq!(receipts.len(), 1);
    assert_eq!(receipts[0].finality_height, 3);
}

// ─── Merge with Equivocator Blocks ─────────────────────────────────────────

#[test]
fn merge_equivocator_blocks_marks_equivocator() {
    let key_a = random_key();
    let key_b = random_key();
    let creator_b = key_b.verifying_key().to_bytes();

    let mut lace = Blocklace::new_simple(key_a);

    // Create two conflicting blocks from B.
    let b1 = Block::new(&key_b, 1, Payload::Data(b"version A".to_vec()), vec![]);
    let b2 = Block::new(&key_b, 1, Payload::Data(b"version B".to_vec()), vec![]);

    // Merge both at once (simulating receiving a delta from a peer who saw both).
    let result = lace.merge(vec![b1, b2]);
    // Merge succeeds (inserts both as evidence) but the equivocator is detected.
    assert!(result.is_ok());
    assert!(lace.is_equivocator(&creator_b));
    assert_eq!(lace.len(), 2); // Both blocks kept as evidence
}

#[test]
fn merge_removes_tip_on_equivocation_detection() {
    // Closes audit gap C: merge() must mirror receive_block()'s tip removal.
    let key_a = random_key();
    let key_b = random_key();
    let creator_b = key_b.verifying_key().to_bytes();

    let mut lace = Blocklace::new_simple(key_a);

    // Build three blocks: a good seq-1, a CONFLICTING seq-1, and a seq-2.
    // If merge fails to consult `equivocators` when deciding tips, the
    // seq-2 block from B (which arrives after the equivocation was
    // detected within this same merge) will set tips[B] = seq-2, leaving
    // dissemination/frontier state inconsistent with B's eviction.
    let b1_good = Block::new(&key_b, 1, Payload::Data(b"good".to_vec()), vec![]);
    let b1_bad = Block::new(&key_b, 1, Payload::Data(b"bad".to_vec()), vec![]);
    let b2 = Block::new(&key_b, 2, Payload::Data(b"after".to_vec()), vec![]);

    let result = lace.merge(vec![b1_good, b1_bad, b2]);
    assert!(result.is_ok());
    assert!(lace.is_equivocator(&creator_b));
    assert!(
        !lace.tips().contains_key(&creator_b),
        "tip for equivocator must be removed by merge (audit gap C)"
    );
}

#[test]
fn round_of_returns_dag_depth() {
    let key_a = random_key();
    let key_b = random_key();
    let mut lace = Blocklace::new_simple(key_a.clone());

    // Genesis block from A (round 1).
    let block0 = lace.add_block(Payload::Data(b"genesis".to_vec()));
    let r0 = lace.round_of(&block0.id()).expect("round for genesis");
    assert_eq!(r0, 1);

    // A second block from A predecessing block0 (round 2).
    let block1 = lace.add_block(Payload::Data(b"second".to_vec()));
    let r1 = lace.round_of(&block1.id()).expect("round for block1");
    assert_eq!(r1, 2);

    // A block from B predecessing both A's blocks (round 3).
    let block2 = Block::new(
        &key_b,
        1,
        Payload::Data(b"b1".to_vec()),
        vec![block0.id(), block1.id()],
    );
    lace.receive_block(block2.clone()).expect("receive block2");
    let r2 = lace.round_of(&block2.id()).expect("round for block2");
    assert_eq!(r2, 3);
}
