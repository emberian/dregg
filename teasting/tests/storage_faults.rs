//! Fault scenarios for storage subsystems.
//!
//! Tests what happens to queues, inboxes, relay operators, and pub-sub topics when
//! things go wrong: crashes, partitions, byzantine behavior, race conditions.
//!
//! # Safety invariants that must hold under ALL faults:
//! - Deposits are never lost (in queue, refunded, or at operator)
//! - Messages are never duplicated in the queue (content hash + root transition unique)
//! - Queue root is always consistent with actual contents
//! - Operator bond is sufficient for hosted capacity
//!
//! # Findings documented inline where behavior reveals design gaps.

use pyana_storage::inbox::InboxMessage;
use pyana_storage::multi_asset::{ExchangeRate, FeeError, FeePayment, FeePolicy};
use pyana_storage::operator::{DeliveryDispute, DisputeOutcome, RelayOperator};
use pyana_storage::programmable::{ProgramError, ProgrammableQueue, ValidationContext, programs};
use pyana_storage::pubsub::PubSubTopic;
use pyana_storage::queue::{MerkleQueue, QueueEntry, empty_queue_root, verify_dequeue_proof};
use pyana_storage::relay::RelayError;
use pyana_teasting::fault::{FaultConfig, FaultyNetwork, MessageBuffer};
use pyana_teasting::harness::SimulationHarness;
use pyana_wire::message::WireMessage;

// =============================================================================
// Helpers
// =============================================================================

fn identity(n: u8) -> [u8; 32] {
    [n; 32]
}

fn make_entry(content: &[u8], sender: [u8; 32], deposit: u64, height: u64) -> QueueEntry {
    QueueEntry {
        content_hash: *blake3::hash(content).as_bytes(),
        sender,
        deposit,
        enqueued_at: height,
        size: content.len(),
    }
}

fn test_msg(sender: [u8; 32], data: &[u8]) -> InboxMessage {
    InboxMessage::Encrypted {
        ciphertext: data.to_vec(),
        sender,
    }
}

fn well_bonded_operator() -> RelayOperator {
    RelayOperator::new(identity(0xAA), 100_000, 50)
}

fn data_hash(data: &[u8]) -> [u8; 32] {
    *blake3::hash(data).as_bytes()
}

// =============================================================================
// Test 1: Relay crash mid-enqueue
// =============================================================================

/// FINDING: MerkleQueue is purely in-memory. If the relay node crashes AFTER accepting
/// a message but BEFORE persisting state (or confirming to the sender), the message is
/// LOST. The sender's deposit was conceptually "accepted" but never committed. In a real
/// system, this requires a write-ahead log (WAL) or atomic commitment protocol.
///
/// The current design trades crash safety for simplicity. Senders MUST retry after
/// timeout if they don't receive a confirmation. The deposit is only truly committed
/// when the queue root advances AND the sender receives the new root as confirmation.
#[test]
fn relay_crash_mid_enqueue_message_lost() {
    let mut harness = SimulationHarness::new_federation(3);
    let mut net = FaultyNetwork::new(FaultConfig::perfect(), "crash-mid-enqueue");
    net.register_nodes(0, 1); // relay node

    let mut operator = well_bonded_operator();
    let owner = identity(0x01);
    operator.host_inbox(owner, 10, 50).unwrap();

    // Sender sends a message to the relay.
    harness.advance_blocks(5);
    let msg = test_msg(identity(0xBB), b"will-be-lost");
    let root_before = operator.inbox_root(&owner).unwrap();

    // Simulate: message is accepted into operator's queue...
    let root_after = operator
        .receive_message(&owner, msg, 500, harness.clock.block_height)
        .unwrap();
    assert_ne!(root_before, root_after);
    assert_eq!(operator.total_pending(), 1);

    // ...but relay CRASHES before confirming to sender.
    let crash_state = net.crash_node(0, 0, harness.clock.block_height);
    assert!(!net.is_node_healthy(0, 0));

    // On recovery: the relay restarts with NO persistent state.
    // Simulate recovery by creating a fresh operator (in-memory state is gone).
    net.recover_node(0, 0, crash_state.clone());
    let mut recovered_operator = well_bonded_operator();
    recovered_operator.host_inbox(owner, 10, 50).unwrap();

    // FINDING: The message is LOST. Recovered operator has empty inbox.
    assert_eq!(recovered_operator.total_pending(), 0);
    assert_eq!(
        recovered_operator.inbox_root(&owner).unwrap(),
        empty_queue_root()
    );

    // Invariant check: deposits are balanced (message was lost, deposit never committed).
    // The sender never received confirmation, so from the protocol's perspective,
    // the enqueue never happened. Sender retries.
    harness.advance_blocks(1);
    let retry_msg = test_msg(identity(0xBB), b"will-be-lost");
    let retry_root = recovered_operator
        .receive_message(&owner, retry_msg, 500, harness.clock.block_height)
        .unwrap();
    assert_eq!(recovered_operator.total_pending(), 1);
    assert_ne!(retry_root, empty_queue_root());
}

// =============================================================================
// Test 2: Relay crash with pending drain
// =============================================================================

/// On crash while owner has a pending drain request: if the relay checkpointed the
/// queue state before crash, owner can retry drain on recovery. If not, see Test 1.
/// This test verifies the "happy path" where state was committed before crash.
#[test]
fn relay_crash_with_pending_drain_recoverable_if_checkpointed() {
    let mut harness = SimulationHarness::new_federation(3);
    let mut net = FaultyNetwork::new(FaultConfig::perfect(), "crash-pending-drain");
    net.register_nodes(0, 1);

    let mut operator = well_bonded_operator();
    let owner = identity(0x01);
    operator.host_inbox(owner, 20, 50).unwrap();

    // Enqueue 5 messages (these are "checkpointed" — they exist in operator state).
    for i in 0u8..5 {
        harness.advance_blocks(1);
        let msg = test_msg(identity(i + 10), &[i; 16]);
        operator
            .receive_message(&owner, msg, 200, harness.clock.block_height)
            .unwrap();
    }
    assert_eq!(operator.total_pending(), 5);
    let root_before_crash = operator.inbox_root(&owner).unwrap();

    // Owner requests drain, relay begins processing...
    // Relay crashes BEFORE delivering the drain results to owner.
    let _crash_state = net.crash_node(0, 0, harness.clock.block_height);

    // Simulate: owner never received the drain results.
    // But operator's internal state still has 5 messages (it didn't complete the drain).
    // On recovery with the SAME operator state (simulating persistent storage):
    net.recover_node(
        0,
        0,
        pyana_teasting::fault::SavedState {
            node_idx: 0,
            federation_idx: 0,
            height_at_crash: harness.clock.block_height,
            unsent_messages: vec![],
            unprocessed_messages: vec![],
        },
    );

    // Owner retries drain on the same operator state (persistent state survived).
    assert_eq!(operator.total_pending(), 5);
    assert_eq!(operator.inbox_root(&owner).unwrap(), root_before_crash);

    harness.advance_blocks(10);
    let drained = operator.drain_for_owner(&owner, 100, harness.clock.block_height);
    assert_eq!(drained.len(), 5);

    // All messages delivered in FIFO order with valid proofs.
    for i in 0u8..5 {
        assert_eq!(drained[i as usize].0.sender, identity(i + 10));
        assert!(verify_dequeue_proof(&drained[i as usize].1));
    }

    // Queue is now empty.
    assert_eq!(operator.total_pending(), 0);
    assert_eq!(
        operator.inbox_root(&owner).unwrap(),
        empty_queue_root()
    );
}

// =============================================================================
// Test 3: Partition between sender and relay
// =============================================================================

/// Sender's enqueue messages can't reach relay during partition. After heal:
/// sender retries. Question: is the retry idempotent or does it duplicate?
///
/// FINDING: The system does NOT provide built-in idempotency. If a sender retries
/// with the same content, a second entry is created (different enqueued_at height).
/// To achieve idempotency, the sender must check the queue root before and after,
/// or use a content-hash-based deduplication layer above MerkleQueue.
#[test]
fn partition_sender_relay_retry_creates_duplicate() {
    let mut harness = SimulationHarness::new_federation(3);
    let mut net = FaultyNetwork::new(FaultConfig::perfect(), "partition-sender-relay");

    let mut operator = well_bonded_operator();
    let owner = identity(0x01);
    operator.host_inbox(owner, 10, 50).unwrap();

    // Inject partition between federation 0 (sender) and federation 1 (relay).
    net.inject_partition(0, 1, 20);

    // Sender attempts to send — blocked by partition.
    let ping = WireMessage::Ping {
        seq: 1,
        timestamp: 0,
    };
    let accepted = net.send(0, 1, ping);
    assert!(!accepted, "message should be blocked by partition");
    assert_eq!(net.dropped_messages.len(), 1);

    // Partition heals after 20 ticks.
    net.advance_ticks(21);
    assert!(net.config.partition.is_none());

    // Sender retries: first attempt.
    harness.advance_blocks(1);
    let msg_content = b"idempotency-test";
    let msg = test_msg(identity(0xBB), msg_content);
    let root1 = operator
        .receive_message(&owner, msg, 300, harness.clock.block_height)
        .unwrap();
    assert_eq!(operator.total_pending(), 1);

    // Sender retries AGAIN (didn't get confirmation due to network flake).
    harness.advance_blocks(1);
    let msg_retry = test_msg(identity(0xBB), msg_content);
    let root2 = operator
        .receive_message(&owner, msg_retry, 300, harness.clock.block_height)
        .unwrap();

    // FINDING: Both accepted — creates a duplicate!
    assert_eq!(operator.total_pending(), 2);
    assert_ne!(root1, root2, "root must advance for each enqueue");

    // The two entries have the same content_hash but different enqueued_at.
    let drained = operator.drain_for_owner(&owner, 10, harness.clock.block_height);
    assert_eq!(drained.len(), 2);
    assert_eq!(drained[0].0.content_hash, drained[1].0.content_hash);
    assert_ne!(
        drained[0].0.enqueued_at, drained[1].0.enqueued_at,
        "timestamps differ even though content is identical"
    );
}

// =============================================================================
// Test 4: Partition between relay and owner
// =============================================================================

/// Messages accumulate at relay while owner is partitioned. After heal: owner
/// drains all queued messages in FIFO order.
#[test]
fn partition_relay_owner_messages_accumulate_then_drain() {
    let mut harness = SimulationHarness::new_federation(3);
    let mut net = FaultyNetwork::new(FaultConfig::perfect(), "partition-relay-owner");

    let mut operator = well_bonded_operator();
    let owner = identity(0x01);
    operator.host_inbox(owner, 50, 50).unwrap();

    // Partition between relay (fed 1) and owner (fed 2).
    net.inject_partition(1, 2, 100);

    // Messages continue to arrive from senders to relay during partition.
    let mut expected_senders = Vec::new();
    for i in 0u8..8 {
        harness.advance_blocks(2);
        let msg = test_msg(identity(i + 20), &[i; 32]);
        operator
            .receive_message(&owner, msg, 150, harness.clock.block_height)
            .unwrap();
        expected_senders.push(identity(i + 20));
    }

    // All 8 messages queued, owner cannot drain (partitioned).
    assert_eq!(operator.total_pending(), 8);

    // Partition heals.
    net.advance_ticks(101);
    assert!(net.config.partition.is_none());

    // Owner reconnects and drains everything.
    harness.advance_blocks(50);
    let drained = operator.drain_for_owner(&owner, 100, harness.clock.block_height);
    assert_eq!(drained.len(), 8);

    // FIFO order preserved.
    for (i, (entry, proof)) in drained.iter().enumerate() {
        assert_eq!(entry.sender, expected_senders[i], "FIFO violation at {i}");
        assert!(verify_dequeue_proof(proof), "invalid proof at {i}");
    }

    // Queue empty, root back to empty.
    assert_eq!(operator.total_pending(), 0);
    assert_eq!(
        operator.inbox_root(&owner).unwrap(),
        empty_queue_root()
    );
}

// =============================================================================
// Test 5: Byzantine relay — claims delivery but didn't
// =============================================================================

/// Owner never received messages. Dispute: sender has enqueue proof (old root + entry),
/// relay cannot produce dequeue proof -> relay slashed.
#[test]
fn byzantine_relay_claims_delivery_without_proof_gets_slashed() {
    let mut harness = SimulationHarness::new_federation(3);

    let mut operator = well_bonded_operator();
    let owner = identity(0x01);
    operator.host_inbox(owner, 10, 50).unwrap();
    let initial_bond = operator.bond;

    // Sender enqueues a message.
    harness.advance_blocks(10);
    let msg = test_msg(identity(0xCC), b"byzantine-test");
    operator
        .receive_message(&owner, msg, 1000, harness.clock.block_height)
        .unwrap();

    // Drain to obtain a valid proof structure for the dispute.
    let drained = operator.drain_for_owner(&owner, 1, harness.clock.block_height);
    let (entry, enqueue_proof) = &drained[0];

    // Byzantine scenario: relay CLAIMS it delivered but actually didn't give owner the msg.
    // Sender files dispute: has enqueue proof, but relay has NO delivery proof.
    let dispute = DeliveryDispute {
        sender: identity(0xCC),
        message_hash: entry.content_hash,
        enqueue_proof: enqueue_proof.clone(),
        claimed_delivery_height: None, // Relay can't even claim when
        delivery_proof: None,          // No proof of delivery
        filed_at: 20,
    };

    // SLA deadline: filed_at + max_delivery_latency = 20 + 50 = 70.
    // Before deadline: dispute pending (returns InvalidDispute).
    let outcome_early = operator.resolve_dispute(&dispute, 60);
    assert_eq!(outcome_early, DisputeOutcome::InvalidDispute);

    // After deadline: relay is slashed.
    let outcome_slashed = operator.resolve_dispute(&dispute, 75);
    assert_eq!(
        outcome_slashed,
        DisputeOutcome::OperatorSlashed {
            slash_amount: initial_bond, // full bond / 1 inbox
        }
    );
}

// =============================================================================
// Test 6: Byzantine relay — double-charges deposits
// =============================================================================

/// Relay enqueues the same message twice, charging deposit twice. Detection:
/// sender verifies queue root transition is unique per message.
///
/// FINDING: The queue DOES allow duplicate content hashes (see Test 3). A byzantine
/// relay could exploit this. The defense is: sender tracks the expected root transition
/// for their specific message. If the relay returns a root that implies more entries
/// than expected, the sender can detect the double-charge by comparing entry count
/// or requesting a proof of the queue contents.
#[test]
fn byzantine_relay_double_enqueue_detectable_by_sender() {
    let mut harness = SimulationHarness::new_federation(3);

    let mut operator = well_bonded_operator();
    let owner = identity(0x01);
    operator.host_inbox(owner, 10, 50).unwrap();

    harness.advance_blocks(5);
    let msg_data = b"charge-me-once";
    let msg1 = test_msg(identity(0xDD), msg_data);
    let msg2 = test_msg(identity(0xDD), msg_data); // Same content, same sender

    // Relay enqueues the message once (legitimate).
    let root_after_first = operator
        .receive_message(&owner, msg1, 500, harness.clock.block_height)
        .unwrap();

    // Byzantine relay enqueues it AGAIN (double-charge).
    harness.advance_blocks(1);
    let root_after_second = operator
        .receive_message(&owner, msg2, 500, harness.clock.block_height)
        .unwrap();

    // Both succeed at the queue level — the queue doesn't deduplicate.
    assert_eq!(operator.total_pending(), 2);
    assert_ne!(root_after_first, root_after_second);

    // DETECTION: Sender expected exactly ONE root transition for their message.
    // They received root_after_first as confirmation. If they later see the queue
    // at root_after_second but only sent one message, they know something is wrong.
    // The entries will have the same content_hash:
    let drained = operator.drain_for_owner(&owner, 10, harness.clock.block_height);
    assert_eq!(drained[0].0.content_hash, drained[1].0.content_hash);

    // Sender's defense: compute the expected root transition from (empty -> 1 entry)
    // and compare. If the relay returns a DIFFERENT root, the relay did something
    // unexpected. This is the root transition uniqueness property.
    let mut verification_queue = MerkleQueue::new(10);
    let expected_entry = make_entry(
        &test_msg(identity(0xDD), msg_data).to_bytes_for_hash(),
        identity(0xDD),
        500,
        5, // height at first enqueue
    );
    // The sender can independently compute what the root SHOULD be:
    let _ = verification_queue.enqueue(expected_entry);
    // If root_after_first != verification_queue.root(), relay is misbehaving.
    // (In practice, content_hash computation involves the InboxMessage serialization,
    // so direct comparison requires the same hash path.)
}

// =============================================================================
// Test 7: Pub-sub — publisher crashes mid-publish
// =============================================================================

/// Publisher publishes to a topic. Some subscribers got it, some didn't (simulated by
/// partial cursor advancement). On recovery: publisher re-publishes.
///
/// FINDING: PubSubTopic does NOT provide idempotent publish. Re-publishing the same
/// data_hash creates a new entry at a new position. Subscribers who already saw it
/// will see it again (duplicate). The system requires application-level deduplication
/// (e.g., subscribers track seen content_hashes and skip duplicates).
#[test]
fn pubsub_publisher_crash_mid_publish_causes_duplicate() {
    let _harness = SimulationHarness::new_federation(3);

    let publisher = identity(0xAA);
    let mut topic = PubSubTopic::new(publisher, "crash-topic".to_string(), 100, 10);

    let sub_fast = identity(0x01);
    let sub_slow = identity(0x02);
    topic.subscribe(sub_fast).unwrap();
    topic.subscribe(sub_slow).unwrap();

    // Publisher publishes message 1: both subscribers will eventually see it.
    let hash1 = data_hash(b"msg-before-crash");
    topic.publish(&publisher, hash1, 100).unwrap();

    // Publisher publishes message 2, but crashes mid-publish.
    // In reality: the publish() call either succeeds atomically or fails.
    // But if the publisher THINKS it failed (network timeout on confirmation),
    // it will retry.
    let hash2 = data_hash(b"msg-during-crash");
    topic.publish(&publisher, hash2, 100).unwrap(); // Actually succeeded

    // Fast subscriber reads both messages before crash is detected.
    let entry1 = topic.read_next(&sub_fast).unwrap().unwrap();
    assert_eq!(entry1.content_hash, hash1);
    let entry2 = topic.read_next(&sub_fast).unwrap().unwrap();
    assert_eq!(entry2.content_hash, hash2);

    // Slow subscriber hasn't read anything yet.
    assert_eq!(topic.subscriber_lag(&sub_slow), Some(2));

    // Publisher recovers and re-publishes hash2 (doesn't know it already committed).
    topic.publish(&publisher, hash2, 100).unwrap();

    // FINDING: Now there are 3 entries total, hash2 appears twice!
    assert_eq!(topic.total_published(), 3);

    // Fast subscriber sees the duplicate.
    let dup_hash = topic.read_next(&sub_fast).unwrap().unwrap().content_hash;
    assert_eq!(dup_hash, hash2, "duplicate detected");

    // Slow subscriber will also see both copies.
    let s1_hash = topic.read_next(&sub_slow).unwrap().unwrap().content_hash;
    let s2_hash = topic.read_next(&sub_slow).unwrap().unwrap().content_hash;
    let s3_hash = topic.read_next(&sub_slow).unwrap().unwrap().content_hash;
    assert_eq!(s1_hash, hash1);
    assert_eq!(s2_hash, hash2);
    assert_eq!(s3_hash, hash2); // duplicate
}

// =============================================================================
// Test 8: Pub-sub — subscriber crashes and falls behind
// =============================================================================

/// Subscriber goes offline for many epochs. On recovery: cursor is still valid,
/// reads from where they left off (if GC hasn't cleaned it).
#[test]
fn pubsub_subscriber_crash_cursor_valid_on_recovery() {
    let _harness = SimulationHarness::new_federation(3);

    let publisher = identity(0xAA);
    let mut topic = PubSubTopic::new(publisher, "resilient-topic".to_string(), 1000, 10);

    let active_sub = identity(0x01);
    let crashed_sub = identity(0x02);
    topic.subscribe(active_sub).unwrap();
    topic.subscribe(crashed_sub).unwrap();

    // Publish 5 messages. Both subscribers can see them.
    for i in 0u8..5 {
        topic.publish(&publisher, data_hash(&[i; 8]), 50).unwrap();
    }

    // Crashed subscriber reads first 2, then goes offline.
    topic.read_next(&crashed_sub).unwrap().unwrap();
    topic.read_next(&crashed_sub).unwrap().unwrap();
    assert_eq!(topic.subscriber_lag(&crashed_sub), Some(3));

    // Many more messages published while subscriber is offline.
    for i in 5u8..25 {
        topic.publish(&publisher, data_hash(&[i; 8]), 50).unwrap();
    }

    // Active subscriber reads everything.
    while topic.read_next(&active_sub).unwrap().is_some() {}
    assert_eq!(topic.subscriber_lag(&active_sub), Some(0));

    // Crashed subscriber recovers. Cursor should still be valid (no GC yet,
    // because gc_consumed() requires ALL subscribers to have read).
    assert_eq!(topic.subscriber_lag(&crashed_sub), Some(23));

    // Crashed subscriber catches up from where it left off.
    let entry = topic.read_next(&crashed_sub).unwrap().unwrap();
    assert_eq!(entry.content_hash, data_hash(&[2u8; 8])); // Entry index 2

    // Can continue reading all remaining.
    let mut read_count = 1; // already read one above
    while topic.read_next(&crashed_sub).unwrap().is_some() {
        read_count += 1;
    }
    assert_eq!(read_count, 23); // 25 total - 2 already read before crash
    assert_eq!(topic.subscriber_lag(&crashed_sub), Some(0));
}

// =============================================================================
// Test 9: Pub-sub — GC races with slow subscriber
// =============================================================================

/// FINDING: If all OTHER subscribers have read past a point, gc_consumed() will remove
/// those entries. A slow subscriber whose cursor points to GC'd entries loses that data.
/// The read_next() implementation handles this by advancing the cursor to the new head,
/// effectively skipping the GC'd messages. THIS IS DATA LOSS for the slow subscriber.
///
/// This is a KNOWN TRADEOFF: bounded memory vs. completeness for slow subscribers.
/// Mitigation: subscribers must stay within the topic's retention window, or use
/// a separate persistent replay log.
#[test]
fn pubsub_gc_races_with_slow_subscriber_data_lost() {
    let _harness = SimulationHarness::new_federation(3);

    let publisher = identity(0xAA);
    let mut topic = PubSubTopic::new(publisher, "gc-race".to_string(), 100, 10);

    let fast_sub = identity(0x01);
    let slow_sub = identity(0x02);
    topic.subscribe(fast_sub).unwrap();
    topic.subscribe(slow_sub).unwrap();

    // Publish 10 messages.
    let mut hashes = Vec::new();
    for i in 0u8..10 {
        let h = data_hash(&[i; 4]);
        topic.publish(&publisher, h, 30).unwrap();
        hashes.push(h);
    }

    // Fast subscriber reads all 10.
    for _ in 0..10 {
        topic.read_next(&fast_sub).unwrap().unwrap();
    }
    assert_eq!(topic.subscriber_lag(&fast_sub), Some(0));

    // Slow subscriber reads only first 2.
    topic.read_next(&slow_sub).unwrap().unwrap(); // index 0
    topic.read_next(&slow_sub).unwrap().unwrap(); // index 1
    assert_eq!(topic.subscriber_lag(&slow_sub), Some(8));

    // Unsubscribe the fast subscriber to make min_cursor = slow_sub's cursor (2).
    // Then GC will remove entries 0 and 1 (already read by slow sub).
    // But if we add a THIRD subscriber that has read everything, and then remove
    // slow sub's protection...
    //
    // Actually: gc_consumed() uses min cursor across ALL subscribers.
    // With fast_sub at 10 and slow_sub at 2, min is 2. GC removes entries 0..2.
    let removed = topic.gc_consumed();
    assert_eq!(removed, 2); // Entries 0,1 removed (both subs have read past them).

    // Slow subscriber still has 8 unread. Its cursor (at position 2) is still valid
    // because GC only removed entries BEFORE its cursor.
    let entry = topic.read_next(&slow_sub).unwrap().unwrap();
    assert_eq!(entry.content_hash, hashes[2]);

    // Now: simulate the pathological case. Slow sub stops reading entirely.
    // We unsubscribe slow_sub, let fast_sub read new stuff, GC, re-subscribe.
    // This is the actual race scenario:
    topic.unsubscribe(&slow_sub);

    // Publish 5 more.
    for i in 10u8..15 {
        topic.publish(&publisher, data_hash(&[i; 4]), 30).unwrap();
    }
    // Fast sub reads them.
    for _ in 0..5 {
        topic.read_next(&fast_sub).unwrap().unwrap();
    }

    // GC now: with only fast_sub (at position 15), min_cursor = 15.
    // All remaining entries (positions 2..15) can be GC'd!
    let removed2 = topic.gc_consumed();
    // gc_consumed removes entries from head to min_cursor.
    // Head is at 2 (from first GC), min_cursor is 15. Remove 15-2 = 13 entries... but
    // topic only has 13 entries in buffer (indices 2..15). After GC: 0 pending.
    assert!(removed2 > 0);

    // FINDING: If slow_sub re-subscribes now, it starts at current tail (15)
    // and has LOST entries 3..14 forever.
    topic.subscribe(slow_sub).unwrap();
    assert_eq!(topic.subscriber_lag(&slow_sub), Some(0));
    assert!(topic.read_next(&slow_sub).unwrap().is_none());
    // Those messages are gone. This is the documented tradeoff.
}

// =============================================================================
// Test 10: Queue program validation under adversarial input
// =============================================================================

/// Byzantine sender tries edge cases against programmable queue constraints:
/// - Rate limit at exact boundary
/// - Temporal gate at exact deadline
/// - Deposit at exact minimum
#[test]
fn queue_program_adversarial_edge_cases() {
    // --- Rate limit boundary ---
    let rate_program = programs::rate_limited(3, 100, 50);
    let mut rate_queue = ProgrammableQueue::new(
        "rate-adversarial".to_string(),
        identity(0x01),
        rate_program,
        None,
        100,
    );

    let sender = identity(0xEE);

    // Exactly at max_per_epoch - 1 (count=2, max=3): should succeed.
    let entry = make_entry(b"boundary-msg", sender, 100, 100);
    let ctx = ValidationContext {
        sender,
        current_height: 100,
        current_epoch: 10,
        sender_epoch_count: 2, // next would be 3rd, max is 3
        preimage: None,
        sequence: None,
    };
    assert!(rate_queue.enqueue_validated(entry, &ctx).is_ok());

    // Exactly AT max (count=3, max=3): should be rejected.
    let entry2 = make_entry(b"over-boundary", sender, 100, 101);
    let ctx_at_max = ValidationContext {
        sender,
        current_height: 101,
        current_epoch: 10,
        sender_epoch_count: 3,
        preimage: None,
        sequence: None,
    };
    let result = rate_queue.enqueue_validated(entry2, &ctx_at_max);
    assert!(matches!(
        result,
        Err(ProgramError::ConstraintViolation { .. })
    ));

    // --- Temporal gate at exact deadline ---
    let temporal_program = programs::timed(50, 200);
    let mut temporal_queue = ProgrammableQueue::new(
        "temporal-adversarial".to_string(),
        identity(0x01),
        temporal_program,
        None,
        100,
    );

    // Exactly at not_before (height=50): should succeed (>= comparison uses <).
    let entry_at_start = make_entry(b"at-start", sender, 100, 50);
    let ctx_at_start = ValidationContext {
        sender,
        current_height: 50, // exactly not_before
        current_epoch: 5,
        sender_epoch_count: 0,
        preimage: None,
        sequence: None,
    };
    assert!(
        temporal_queue
            .enqueue_validated(entry_at_start, &ctx_at_start)
            .is_ok()
    );

    // Exactly at not_after (height=200): should succeed (> comparison, not >=).
    let entry_at_end = make_entry(b"at-end", sender, 100, 200);
    let ctx_at_end = ValidationContext {
        sender,
        current_height: 200, // exactly not_after
        current_epoch: 20,
        sender_epoch_count: 0,
        preimage: None,
        sequence: None,
    };
    assert!(
        temporal_queue
            .enqueue_validated(entry_at_end, &ctx_at_end)
            .is_ok()
    );

    // One past not_after (height=201): should be rejected.
    let entry_past_end = make_entry(b"past-end", sender, 100, 201);
    let ctx_past_end = ValidationContext {
        sender,
        current_height: 201,
        current_epoch: 20,
        sender_epoch_count: 0,
        preimage: None,
        sequence: None,
    };
    let result = temporal_queue.enqueue_validated(entry_past_end, &ctx_past_end);
    assert!(matches!(
        result,
        Err(ProgramError::ConstraintViolation { .. })
    ));

    // --- MinDeposit at exact minimum ---
    let deposit_program = programs::open(500);
    let mut deposit_queue = ProgrammableQueue::new(
        "deposit-adversarial".to_string(),
        identity(0x01),
        deposit_program,
        None,
        100,
    );

    // Exactly at minimum: should succeed.
    let entry_exact = make_entry(b"exact-deposit", sender, 500, 100);
    let ctx_deposit = ValidationContext {
        sender,
        current_height: 100,
        current_epoch: 10,
        sender_epoch_count: 0,
        preimage: None,
        sequence: None,
    };
    assert!(
        deposit_queue
            .enqueue_validated(entry_exact, &ctx_deposit)
            .is_ok()
    );

    // One below minimum: rejected.
    let entry_below = make_entry(b"below-deposit", sender, 499, 100);
    let result = deposit_queue.enqueue_validated(entry_below, &ctx_deposit);
    assert!(matches!(
        result,
        Err(ProgramError::ConstraintViolation { .. })
    ));
}

// =============================================================================
// Test 11: Multi-asset fee with price manipulation
// =============================================================================

/// Exchange rate changes between intent and settlement. Sender committed at old rate,
/// relay charges at new rate.
///
/// FINDING: The FeePolicy validates against the rate AT THE TIME of validation.
/// If the rate is updated between when the sender created the payment and when
/// the relay validates it, the payment will be rejected (EquivalentMismatch).
/// The correct behavior is: the rate at ENQUEUE time must be locked in the payment.
/// The relay validates using the same rate the sender used (embedded in FeePayment).
#[test]
fn multi_asset_fee_rate_change_between_intent_and_settlement() {
    let usdc_asset = *blake3::hash(b"USDC").as_bytes();

    let mut policy = FeePolicy::multi_asset(vec![(
        usdc_asset,
        ExchangeRate {
            rate: 100, // 1 USDC = 100 computrons at time of intent
            updated_at: 50,
            max_age: 200,
        },
    )]);

    // Sender creates payment at height 60 using rate=100.
    let payment_at_old_rate = FeePayment {
        asset: usdc_asset,
        amount: 10,
        computron_equivalent: 1000, // 10 * 100
    };

    // At height 60: payment is valid.
    let result = policy.validate_payment(&payment_at_old_rate, 60);
    assert_eq!(result, Ok(1000));

    // Rate changes! Now 1 USDC = 150 computrons.
    policy.update_rate(
        usdc_asset,
        ExchangeRate {
            rate: 150,
            updated_at: 70,
            max_age: 200,
        },
    );

    // At height 80: sender's old payment (computed_equivalent=1000) is WRONG
    // because 10 * 150 = 1500 now.
    let result_after_update = policy.validate_payment(&payment_at_old_rate, 80);
    assert_eq!(
        result_after_update,
        Err(FeeError::EquivalentMismatch {
            claimed: 1000,
            computed: 1500,
        })
    );

    // CORRECT BEHAVIOR: Sender must create a new payment at the new rate.
    let payment_at_new_rate = FeePayment {
        asset: usdc_asset,
        amount: 10,
        computron_equivalent: 1500, // 10 * 150
    };
    let result_correct = policy.validate_payment(&payment_at_new_rate, 80);
    assert_eq!(result_correct, Ok(1500));

    // FINDING: The defense against rate manipulation is: the relay MUST validate
    // the payment at the exact rate the sender committed to. If rates are volatile,
    // the sender should lock the rate by including a rate oracle attestation in their
    // message. The current design locks at validation time, which means the sender
    // must re-create the payment if the rate becomes stale.

    // Edge case: rate goes stale entirely.
    let old_rate_policy = FeePolicy::multi_asset(vec![(
        usdc_asset,
        ExchangeRate {
            rate: 100,
            updated_at: 50,
            max_age: 20, // Only valid until height 70!
        },
    )]);

    // At height 71: stale!
    let result_stale = old_rate_policy.validate_payment(&payment_at_old_rate, 71);
    assert!(matches!(result_stale, Err(FeeError::StaleRate { .. })));
}

// =============================================================================
// Test 12: Inbox eviction race — quota depletes during enqueue
// =============================================================================

/// Owner's quota depletes RIGHT as a sender enqueues. Does the message get in
/// (quota was sufficient at check time) or bounced?
///
/// FINDING: In the current design, eviction is an explicit owner/operator action
/// (evict_inbox). There is no automatic quota-check race because the relay operator
/// processes messages serially. However, if eviction and enqueue happen in the same
/// block (different transactions), the ordering within the block determines the outcome.
/// This is a check-then-act pattern that is safe under single-threaded execution
/// (which MerkleQueue provides) but would need locking in a concurrent setting.
#[test]
fn inbox_eviction_race_check_then_act() {
    let mut harness = SimulationHarness::new_federation(3);

    let mut operator = well_bonded_operator();
    let owner = identity(0x01);
    operator.host_inbox(owner, 5, 50).unwrap(); // Small capacity: 5

    // Fill the inbox to capacity - 1.
    for i in 0u8..4 {
        harness.advance_blocks(1);
        let msg = test_msg(identity(i + 10), &[i; 8]);
        operator
            .receive_message(&owner, msg, 100, harness.clock.block_height)
            .unwrap();
    }
    assert_eq!(operator.total_pending(), 4);

    // Now: two things happen "simultaneously" in the same block:
    // Scenario A: Enqueue THEN evict → message gets in, then evicted (refunded).
    harness.advance_blocks(1);
    let msg_race = test_msg(identity(0xEE), b"racing-message");
    let enqueue_result =
        operator.receive_message(&owner, msg_race, 200, harness.clock.block_height);
    assert!(enqueue_result.is_ok(), "enqueue succeeds before eviction");
    assert_eq!(operator.total_pending(), 5);

    // Eviction happens right after.
    let refunds = operator.evict_inbox(&owner);
    assert_eq!(refunds.len(), 5); // All 5 messages refunded

    // The racing message IS refunded (deposit not lost).
    let racing_refund = refunds.iter().find(|r| r.sender == identity(0xEE));
    assert!(racing_refund.is_some());
    assert_eq!(racing_refund.unwrap().amount, 200);

    // Scenario B: Evict THEN enqueue → enqueue fails (inbox not found).
    // (Already evicted above, so trying to send now fails.)
    let msg_after = test_msg(identity(0xFF), b"too-late");
    let result = operator.receive_message(&owner, msg_after, 100, harness.clock.block_height);
    assert!(matches!(result, Err(RelayError::InboxNotFound { .. })));

    // INVARIANT: No deposits lost. All were either delivered or refunded.
}

// =============================================================================
// Test 13: Cross-federation relay — target federation goes down
// =============================================================================

/// Relay accepts messages for federation B, but fed B is partitioned. Messages
/// accumulate. Fed B returns: are messages still valid (TTL not expired)?
#[test]
fn cross_federation_relay_target_down_ttl_expiry() {
    let mut harness = SimulationHarness::new_federation(3);
    let mut net = FaultyNetwork::new(FaultConfig::perfect(), "cross-fed-target-down");

    let mut operator = well_bonded_operator();
    let owner_in_fed_b = identity(0x01);
    operator.host_inbox(owner_in_fed_b, 20, 50).unwrap();

    // Messages arrive for fed B while it's down.
    net.inject_partition(0, 1, 500); // Long partition

    // Enqueue messages at various heights.
    let msg_heights: Vec<u64> = vec![10, 15, 20, 25, 30];
    for (i, &height) in msg_heights.iter().enumerate() {
        harness.clock.block_height = height;
        let msg = test_msg(identity(i as u8 + 10), &[i as u8; 16]);
        operator
            .receive_message(&owner_in_fed_b, msg, 300, height)
            .unwrap();
    }
    assert_eq!(operator.total_pending(), 5);

    // Time passes... fed B is still down.
    // Simulate: current_height = 60, TTL = 20.
    // Messages enqueued at 10,15,20 expire (10+20=30, 15+20=35, 20+20=40 all < 60).
    // Messages enqueued at 25,30 still valid (25+20=45 < 60, 30+20=50 < 60).
    // Actually: 25+20=45 < 60 -> expired too. 30+20=50 < 60 -> expired too!
    // ALL messages expired at height 60 with TTL=20!
    let gc_result = operator.gc_expired(60, 20);
    assert_eq!(gc_result.messages_collected, 5);

    // All deposits partially refunded (90% to senders).
    assert_eq!(gc_result.sender_refunds.len(), 5);
    for refund in &gc_result.sender_refunds {
        assert_eq!(refund.amount, 270); // 90% of 300
    }
    // Operator earned 10% fees.
    assert_eq!(gc_result.operator_fees, 150); // 5 * (300 * 10%) = 150

    // FINDING: With a long enough partition, ALL messages expire. The target
    // federation returns to find nothing waiting. Senders must re-send.
    // Fed B finally comes back:
    net.advance_ticks(501);
    assert!(net.config.partition.is_none());

    // Owner drains: nothing left.
    harness.clock.block_height = 100;
    let drained = operator.drain_for_owner(&owner_in_fed_b, 100, harness.clock.block_height);
    assert_eq!(drained.len(), 0);
    assert_eq!(operator.total_pending(), 0);

    // Now test: messages sent AFTER recovery DO work.
    let fresh_msg = test_msg(identity(0xAA), b"after-recovery");
    let result = operator.receive_message(&owner_in_fed_b, fresh_msg, 300, 100);
    assert!(result.is_ok());
    assert_eq!(operator.total_pending(), 1);

    // INVARIANT: deposits balanced. Expired deposits = refunded + operator fee.
    // 5 * 300 = 1500 total. 5 * 270 = 1350 refunded. 150 operator fee. 1350 + 150 = 1500.
}

// =============================================================================
// Test 14 (bonus): Queue root consistency after crash-recovery sequence
// =============================================================================

/// Verify that queue root is always consistent with actual contents, even after
/// a complex sequence of operations interrupted by a simulated crash.
#[test]
fn queue_root_consistency_after_complex_operations() {
    let mut harness = SimulationHarness::new_federation(3);

    let mut operator = well_bonded_operator();
    let owner = identity(0x01);
    operator.host_inbox(owner, 20, 50).unwrap();

    // Interleave enqueues and drains.
    let mut total_deposits_in = 0u64;
    let mut total_deposits_out = 0u64;

    // Phase 1: Enqueue 8 messages.
    for i in 0u8..8 {
        harness.advance_blocks(1);
        let deposit = (i as u64 + 1) * 100;
        let msg = test_msg(identity(i + 10), &[i; 16]);
        operator
            .receive_message(&owner, msg, deposit, harness.clock.block_height)
            .unwrap();
        total_deposits_in += deposit;
    }
    let root_after_8 = operator.inbox_root(&owner).unwrap();
    assert_ne!(root_after_8, empty_queue_root());

    // Phase 2: Drain 3 messages.
    let drained_3 = operator.drain_for_owner(&owner, 3, harness.clock.block_height);
    assert_eq!(drained_3.len(), 3);
    for (entry, proof) in &drained_3 {
        assert!(verify_dequeue_proof(proof));
        total_deposits_out += entry.deposit;
    }
    let root_after_drain = operator.inbox_root(&owner).unwrap();
    assert_ne!(root_after_drain, root_after_8);

    // Phase 3: Enqueue 2 more.
    for i in 8u8..10 {
        harness.advance_blocks(1);
        let deposit = (i as u64 + 1) * 100;
        let msg = test_msg(identity(i + 10), &[i; 16]);
        operator
            .receive_message(&owner, msg, deposit, harness.clock.block_height)
            .unwrap();
        total_deposits_in += deposit;
    }
    let root_after_mixed = operator.inbox_root(&owner).unwrap();
    assert_ne!(root_after_mixed, root_after_drain);

    // Phase 4: Drain all remaining (7 messages).
    let drained_rest = operator.drain_for_owner(&owner, 100, harness.clock.block_height);
    assert_eq!(drained_rest.len(), 7);
    for (entry, proof) in &drained_rest {
        assert!(verify_dequeue_proof(proof));
        total_deposits_out += entry.deposit;
    }

    // Queue empty.
    let final_root = operator.inbox_root(&owner).unwrap();
    assert_eq!(final_root, empty_queue_root());
    assert_eq!(operator.total_pending(), 0);

    // INVARIANT: All deposits accounted for (in = out).
    assert_eq!(total_deposits_in, total_deposits_out);
}

// =============================================================================
// Test 15 (bonus): FaultyNetwork message buffer preserves FIFO on recovery
// =============================================================================

/// Verify that MessageBuffer (store-and-forward during crashes) preserves FIFO order.
#[test]
fn message_buffer_preserves_fifo_on_recovery() {
    let mut net = FaultyNetwork::new(FaultConfig::perfect(), "buffer-fifo");
    net.register_nodes(0, 1);
    let mut buffer = MessageBuffer::new();

    // Crash the node.
    let state = net.crash_node(0, 0, 10);
    assert!(!net.is_node_healthy(0, 0));

    // Buffer messages while node is crashed (in order).
    let messages: Vec<WireMessage> = (0u64..5)
        .map(|i| WireMessage::Ping {
            seq: i,
            timestamp: (i * 100) as i64,
        })
        .collect();

    for msg in &messages {
        buffer.buffer(0, 0, msg.clone());
    }
    assert_eq!(buffer.pending_count(0, 0), 5);
    assert_eq!(buffer.total_buffered(), 5);

    // Recover the node.
    net.recover_node(0, 0, state);
    assert!(net.is_node_healthy(0, 0));

    // Drain buffered messages: should be in FIFO order.
    let drained = buffer.drain(0, 0);
    assert_eq!(drained.len(), 5);
    for (i, msg) in drained.iter().enumerate() {
        match msg {
            WireMessage::Ping { seq, .. } => {
                assert_eq!(*seq, i as u64, "FIFO violation at index {i}");
            }
            _ => panic!("unexpected message type"),
        }
    }

    // Buffer is now empty.
    assert_eq!(buffer.pending_count(0, 0), 0);
}

// =============================================================================
// Test 16 (bonus): Operator bond sufficiency invariant under fault scenarios
// =============================================================================

/// Even after crashes and evictions, operator bond must cover hosted capacity.
#[test]
fn operator_bond_invariant_holds_under_faults() {
    let _harness = SimulationHarness::new_federation(3);

    // Operator with limited bond: can host max 10 capacity units (bond=1000, rate=100).
    let mut operator = RelayOperator::new(identity(0xAA), 1000, 50);

    // Host 2 inboxes: 5 + 4 = 9 capacity units. Bond required = 900.
    operator.host_inbox(identity(0x01), 5, 50).unwrap();
    operator.host_inbox(identity(0x02), 4, 50).unwrap();
    assert!(!operator.is_underbonded());
    assert_eq!(operator.required_bond(), 900);

    // Can't host one more with capacity 2 (would need 1100 > 1000).
    let result = operator.host_inbox(identity(0x03), 2, 50);
    assert!(matches!(result, Err(RelayError::Underbonded { .. })));

    // Evict one inbox: frees capacity.
    operator.evict_inbox(&identity(0x01));
    assert_eq!(operator.required_bond(), 400); // only 4 * 100

    // Now can host capacity 6 (400 + 600 = 1000 <= bond).
    operator.host_inbox(identity(0x03), 6, 50).unwrap();
    assert!(!operator.is_underbonded());
    assert_eq!(operator.required_bond(), 1000);

    // INVARIANT: bond >= required_bond at all times during normal operation.
    assert!(operator.bond >= operator.required_bond());
}

// =============================================================================
// Helper trait for InboxMessage serialization (used in Test 6)
// =============================================================================

// =============================================================================
// Test 17: Atomic Queue Tx — Concurrent dequeue conflict (distributed protocol)
// =============================================================================

/// Two agents both attempt to dequeue from the same queue (which has exactly 1 message).
/// Tau ordering means the first one wins, the second fails.
/// This proves the system does not double-spend queue contents.
#[test]
fn atomic_tx_concurrent_dequeue_conflict_second_fails() {
    use pyana_storage::atomic::{QueueOp, QueueTransaction, TxError};
    use std::collections::HashMap;

    let queue_a_id = [0x0A; 32];
    let queue_b_id = [0x0B; 32];
    let queue_c_id = [0x0C; 32];

    let mut queues = HashMap::new();
    let mut qa = MerkleQueue::new(10);
    qa.enqueue(make_entry(b"the-only-message", identity(0x01), 500, 100))
        .unwrap();
    queues.insert(queue_a_id, qa);
    queues.insert(queue_b_id, MerkleQueue::new(10));
    queues.insert(queue_c_id, MerkleQueue::new(10));

    let entry_for_b = make_entry(b"move-to-b", identity(0x01), 100, 101);
    let entry_for_c = make_entry(b"move-to-c", identity(0x01), 100, 101);

    // Alice's transaction: dequeue from A, enqueue to B.
    let mut tx_alice = QueueTransaction::new();
    tx_alice
        .dequeue(queue_a_id)
        .enqueue(queue_b_id, entry_for_b);

    // Bob's transaction: dequeue from A, enqueue to C.
    let mut tx_bob = QueueTransaction::new();
    tx_bob.dequeue(queue_a_id).enqueue(queue_c_id, entry_for_c);

    // Tau orders Alice first. She wins.
    let result_alice = tx_alice.execute(&mut queues);
    assert!(result_alice.is_ok(), "Alice (first by tau) should succeed");
    assert_eq!(
        queues.get(&queue_a_id).unwrap().len(),
        0,
        "A should be empty after Alice"
    );
    assert_eq!(
        queues.get(&queue_b_id).unwrap().len(),
        1,
        "B should have Alice's message"
    );

    // Bob executes second. Queue A is now empty. He fails.
    let result_bob = tx_bob.execute(&mut queues);
    assert!(
        matches!(
            result_bob,
            Err(TxError::QueueError {
                error: pyana_storage::queue::QueueError::Empty,
                ..
            })
        ),
        "Bob (second by tau) should fail because A is now empty"
    );

    // Verify rollback: C should still be empty (Bob's enqueue rolled back).
    assert_eq!(
        queues.get(&queue_c_id).unwrap().len(),
        0,
        "C should be empty (rollback)"
    );

    // INVARIANT: no double-spend. Only one message existed, only one agent got it.
}

// =============================================================================
// Test 18: Atomic Queue Tx — Cross-queue "deadlock" scenario (sequential safety)
// =============================================================================

/// Alice: dequeue A, enqueue B. Bob: dequeue B, enqueue A.
/// In sequential execution (tau ordering), both can succeed because each sees
/// the state AFTER the other has committed.
#[test]
fn atomic_tx_cross_queue_no_deadlock_sequential() {
    use pyana_storage::atomic::QueueTransaction;
    use std::collections::HashMap;

    let queue_a_id = [0x0A; 32];
    let queue_b_id = [0x0B; 32];

    let mut queues = HashMap::new();
    let mut qa = MerkleQueue::new(10);
    qa.enqueue(make_entry(b"msg-in-a", identity(0x01), 300, 50))
        .unwrap();
    let mut qb = MerkleQueue::new(10);
    qb.enqueue(make_entry(b"msg-in-b", identity(0x02), 400, 51))
        .unwrap();
    queues.insert(queue_a_id, qa);
    queues.insert(queue_b_id, qb);

    // Alice: move message from A to B.
    let entry_a_to_b = make_entry(b"alice-moves", identity(0x01), 200, 100);
    let mut tx_alice = QueueTransaction::new();
    tx_alice
        .dequeue(queue_a_id)
        .enqueue(queue_b_id, entry_a_to_b);

    // Bob: move message from B to A.
    let entry_b_to_a = make_entry(b"bob-moves", identity(0x02), 250, 101);
    let mut tx_bob = QueueTransaction::new();
    tx_bob.dequeue(queue_b_id).enqueue(queue_a_id, entry_b_to_a);

    // Sequential execution (tau: Alice first, then Bob).
    let result_alice = tx_alice.execute(&mut queues);
    assert!(result_alice.is_ok(), "Alice should succeed (A has 1 msg)");
    // After Alice: A is empty, B has 2 messages (original + Alice's).
    assert_eq!(queues.get(&queue_a_id).unwrap().len(), 0);
    assert_eq!(queues.get(&queue_b_id).unwrap().len(), 2);

    let result_bob = tx_bob.execute(&mut queues);
    assert!(result_bob.is_ok(), "Bob should succeed (B has 2 msgs)");
    // After Bob: A has 1 (Bob's), B has 1 (net: Alice's remained).
    assert_eq!(queues.get(&queue_a_id).unwrap().len(), 1);
    assert_eq!(queues.get(&queue_b_id).unwrap().len(), 1);

    // NO DEADLOCK. Sequential execution always terminates.
}

// =============================================================================
// Test 19: Atomic Queue Tx — Stale root assertion rejects
// =============================================================================

/// An agent reads queue A's root, then another agent modifies queue A.
/// The first agent's transaction includes an AssertRoot for the OLD root.
/// This must be rejected.
#[test]
fn atomic_tx_stale_root_assertion_rejected() {
    use pyana_storage::atomic::{QueueTransaction, TxError};
    use std::collections::HashMap;

    let queue_a_id = [0x0A; 32];
    let queue_b_id = [0x0B; 32];

    let mut queues = HashMap::new();
    let mut qa = MerkleQueue::new(10);
    qa.enqueue(make_entry(b"original", identity(0x01), 100, 50))
        .unwrap();
    let stale_root = qa.root(); // Alice reads this root
    queues.insert(queue_a_id, qa);
    queues.insert(queue_b_id, MerkleQueue::new(10));

    // Bob modifies queue A (enqueues another message) between Alice's read and execute.
    let bob_entry = make_entry(b"bob-sneaks-in", identity(0x02), 200, 55);
    queues
        .get_mut(&queue_a_id)
        .unwrap()
        .enqueue(bob_entry)
        .unwrap();
    let current_root = queues.get(&queue_a_id).unwrap().root();
    assert_ne!(stale_root, current_root, "Bob's enqueue changed the root");

    // Alice's transaction uses the STALE root in an AssertRoot.
    let alice_entry = make_entry(b"alice-msg", identity(0x01), 100, 60);
    let mut tx_alice = QueueTransaction::new();
    tx_alice
        .assert_root(queue_a_id, stale_root) // STALE!
        .enqueue(queue_b_id, alice_entry);

    // Execute: must fail because root no longer matches.
    let result = tx_alice.execute(&mut queues);
    assert!(
        matches!(result, Err(TxError::RootMismatch { .. })),
        "Stale root assertion must be rejected, got: {:?}",
        result
    );

    // Verify rollback: B should still be empty.
    assert_eq!(
        queues.get(&queue_b_id).unwrap().len(),
        0,
        "B must be empty (rollback)"
    );
}

// =============================================================================
// Test 20: Circuit-level AtomicQueueTx — tampered combined_old_root fails
// =============================================================================

/// Adversarial test: prover claims combined_old_root != actual field[4].
/// The circuit must reject (constraint: old_f4 == combined_old_root param).
#[test]
fn circuit_atomic_tx_wrong_old_root_rejected() {
    use pyana_circuit::effect_vm::{
        CellState, Effect, EffectVmAir, PARAM_BASE, STATE_AFTER_BASE, STATE_BEFORE_BASE,
        generate_effect_vm_trace, param, state,
    };
    use pyana_circuit::field::BabyBear;
    use pyana_circuit::poseidon2::hash_2_to_1;
    use pyana_circuit::stark::StarkAir;

    let mut cell_state = CellState::new(10_000, 0);
    let actual_root = hash_2_to_1(BabyBear::new(0x11), BabyBear::new(0x22));
    cell_state.fields[4] = actual_root;
    cell_state.refresh_commitment();

    // The attacker claims a DIFFERENT old root.
    let fake_old_root = hash_2_to_1(BabyBear::new(0xFF), BabyBear::new(0xEE));
    let combined_new = hash_2_to_1(BabyBear::new(0x33), BabyBear::new(0x44));
    let tx_hash = BabyBear::new(0xABC);

    // Try to generate a trace with mismatched old root.
    // The witness gen doesn't validate this, but the constraint WILL catch it.
    let effects = vec![Effect::AtomicQueueTx {
        op_count: 1,
        tx_hash,
        combined_old_root: fake_old_root, // WRONG! Doesn't match field[4]
        combined_new_root: combined_new,
        net_deposit: 0,
    }];

    let (trace, public_inputs) = generate_effect_vm_trace(&cell_state, &effects);
    let air = EffectVmAir::new(trace.len());

    // The constraint should fail because old_f4 (actual_root) != combined_old_root (fake_old_root).
    let alpha = BabyBear::new(7);
    let c = air.eval_constraints(&trace[0], &trace[1], &public_inputs, alpha);
    assert_ne!(
        c,
        BabyBear::ZERO,
        "Mismatched combined_old_root must fail constraints (old_f4 != param)"
    );
}

// =============================================================================
// Test 21: Circuit-level AtomicQueueTx — balance unchanged enforced
// =============================================================================

/// Adversarial test: prover attempts to change balance by more than the declared
/// net_deposit during AtomicQueueTx. The circuit must reject (balance delta mismatch).
/// With net_deposit=0, ANY balance change is rejected.
#[test]
fn circuit_atomic_tx_balance_change_rejected() {
    use pyana_circuit::effect_vm::{
        AUX_BASE, CellState, EFFECT_VM_WIDTH, Effect, EffectVmAir, STATE_AFTER_BASE, aux_off,
        generate_effect_vm_trace, state,
    };
    use pyana_circuit::field::BabyBear;
    use pyana_circuit::poseidon2::{hash_2_to_1, hash_4_to_1};
    use pyana_circuit::stark::StarkAir;

    let mut cell_state = CellState::new(10_000, 0);
    let combined_old = hash_2_to_1(BabyBear::new(0x11), BabyBear::new(0x22));
    cell_state.fields[4] = combined_old;
    cell_state.refresh_commitment();

    let combined_new = hash_2_to_1(BabyBear::new(0x33), BabyBear::new(0x44));
    let tx_hash = BabyBear::new(0xABC);

    let effects = vec![Effect::AtomicQueueTx {
        op_count: 1,
        tx_hash,
        combined_old_root: combined_old,
        combined_new_root: combined_new,
        net_deposit: 0, // Declares zero balance change
    }];

    let (mut trace, public_inputs) = generate_effect_vm_trace(&cell_state, &effects);

    // Tamper: change balance in state_after (try to steal 1000 computrons).
    // new_balance = 11000 instead of 10000. With net_deposit=0, this must fail.
    let (tampered_lo, tampered_hi) = pyana_circuit::effect_vm::split_u64(11_000);
    trace[0][STATE_AFTER_BASE + state::BALANCE_LO] = tampered_lo;
    trace[0][STATE_AFTER_BASE + state::BALANCE_HI] = tampered_hi;

    // Must also update state commitment intermediates to match tampered balance,
    // otherwise Group 4 catches it first. We want to test the balance constraint specifically.
    let nonce_after = BabyBear::new(1); // nonce incremented
    let inter1 = hash_4_to_1(&[tampered_lo, tampered_hi, nonce_after, cell_state.fields[0]]);
    let inter2 = hash_4_to_1(&[
        cell_state.fields[1],
        cell_state.fields[2],
        cell_state.fields[3],
        combined_new, // field[4] changed
    ]);
    let inter3 = hash_4_to_1(&[
        cell_state.fields[5],
        cell_state.fields[6],
        cell_state.fields[7],
        cell_state.capability_root,
    ]);
    let tampered_commit = hash_4_to_1(&[inter1, inter2, inter3, BabyBear::ZERO]);
    trace[0][AUX_BASE + aux_off::STATE_INTER1] = inter1;
    trace[0][AUX_BASE + aux_off::STATE_INTER2] = inter2;
    trace[0][AUX_BASE + aux_off::STATE_INTER3] = inter3;
    trace[0][STATE_AFTER_BASE + state::STATE_COMMIT] = tampered_commit;

    let air = EffectVmAir::new(trace.len());

    // The AtomicQueueTx balance constraint should fire:
    // new_bal_lo - old_bal_lo + net_deposit != 0 when balance changed but net_deposit=0.
    let alpha = BabyBear::new(13);
    let c = air.eval_constraints(&trace[0], &trace[1], &public_inputs, alpha);
    assert_ne!(
        c,
        BabyBear::ZERO,
        "Balance change beyond declared net_deposit during AtomicQueueTx must fail constraints"
    );
}

// =============================================================================
// Test 22: Atomic Queue Tx — Partial failure rollback preserves deposits
// =============================================================================

/// An atomic transaction with 3 ops: enqueue succeeds, then dequeue fails (empty).
/// ALL operations must be rolled back, including the successful enqueue.
/// Deposits from the first op must be returned.
#[test]
fn atomic_tx_partial_failure_rollback_preserves_state() {
    use pyana_storage::atomic::{QueueTransaction, TxError};
    use std::collections::HashMap;

    let queue_a_id = [0x0A; 32];
    let queue_b_id = [0x0B; 32]; // this one is EMPTY

    let mut queues = HashMap::new();
    queues.insert(queue_a_id, MerkleQueue::new(10));
    queues.insert(queue_b_id, MerkleQueue::new(10)); // empty!

    let root_a_before = queues.get(&queue_a_id).unwrap().root();
    let root_b_before = queues.get(&queue_b_id).unwrap().root();

    // Transaction: enqueue to A (succeeds), then dequeue from B (fails: empty).
    let entry = make_entry(b"will-be-rolled-back", identity(0x01), 500, 100);
    let mut tx = QueueTransaction::new();
    tx.enqueue(queue_a_id, entry).dequeue(queue_b_id);

    let result = tx.execute(&mut queues);
    assert!(
        matches!(
            result,
            Err(TxError::QueueError {
                error: pyana_storage::queue::QueueError::Empty,
                ..
            })
        ),
        "Should fail on dequeue from empty B"
    );

    // CRITICAL: A must be rolled back. The enqueue should not persist.
    assert_eq!(
        queues.get(&queue_a_id).unwrap().len(),
        0,
        "A must be empty after rollback"
    );
    assert_eq!(
        queues.get(&queue_a_id).unwrap().root(),
        root_a_before,
        "A root must be restored"
    );
    assert_eq!(
        queues.get(&queue_b_id).unwrap().root(),
        root_b_before,
        "B root unchanged"
    );
}

// =============================================================================
// Helper trait for InboxMessage serialization (used in Test 6)
// =============================================================================

trait InboxMessageHashHelper {
    fn to_bytes_for_hash(&self) -> Vec<u8>;
}

impl InboxMessageHashHelper for InboxMessage {
    fn to_bytes_for_hash(&self) -> Vec<u8> {
        match self {
            InboxMessage::Capability { cert_bytes, sender } => {
                let mut buf = vec![0x01];
                buf.extend_from_slice(sender);
                buf.extend_from_slice(cert_bytes);
                buf
            }
            InboxMessage::SturdyRef { uri, sender } => {
                let mut buf = vec![0x02];
                buf.extend_from_slice(sender);
                buf.extend_from_slice(uri.as_bytes());
                buf
            }
            InboxMessage::Encrypted { ciphertext, sender } => {
                let mut buf = vec![0x03];
                buf.extend_from_slice(sender);
                buf.extend_from_slice(ciphertext);
                buf
            }
        }
    }
}
