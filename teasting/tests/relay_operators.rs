//! Relay operator scenarios in multi-node simulation context.
//!
//! Exercises operator bonding, inbox hosting, message receive/drain,
//! GC fee mechanics, underbonding, delivery disputes, and offline resilience.

use dregg_storage::inbox::InboxMessage;
use dregg_storage::operator::{DeliveryDispute, DisputeOutcome, RelayOperator};
use dregg_storage::queue::{empty_queue_root, verify_dequeue_proof};
use dregg_storage::relay::RelayError;
use dregg_teasting::harness::SimulationHarness;

/// Deterministic identity from a seed byte.
fn identity(n: u8) -> [u8; 32] {
    [n; 32]
}

/// Create an operator with generous bond for testing.
fn well_bonded_operator() -> RelayOperator {
    RelayOperator::new(identity(0xAA), 100_000, 50)
}

/// Create a test message from a sender.
fn test_msg(sender: [u8; 32], data: &[u8]) -> InboxMessage {
    InboxMessage::Encrypted {
        ciphertext: data.to_vec(),
        sender,
    }
}

// ---------------------------------------------------------------------------
// Test 1: Operator bonds and hosts an inbox -> status shows healthy
// ---------------------------------------------------------------------------
#[test]
fn operator_bonds_and_hosts_inbox_healthy() {
    let _harness = SimulationHarness::new_federation(3);

    let mut operator = well_bonded_operator();
    let owner = identity(0x01);

    // Host an inbox with capacity 20, min_deposit 100.
    operator.host_inbox(owner, 20, 100).unwrap();

    // Verify healthy status.
    assert_eq!(operator.active_inbox_count(), 1);
    assert!(!operator.is_underbonded());
    assert_eq!(operator.total_pending(), 0);

    // Inbox root should be empty.
    let root = operator.inbox_root(&owner).unwrap();
    assert_eq!(root, empty_queue_root());
}

// ---------------------------------------------------------------------------
// Test 2: Sender enqueues to hosted inbox -> operator receives
// ---------------------------------------------------------------------------
#[test]
fn sender_enqueues_to_hosted_inbox() {
    let mut harness = SimulationHarness::new_federation(3);

    let mut operator = well_bonded_operator();
    let owner = identity(0x01);
    operator.host_inbox(owner, 10, 100).unwrap();

    // Sender enqueues a message.
    harness.advance_blocks(5);
    let msg = test_msg(identity(0xBB), b"hello operator");
    let new_root = operator
        .receive_message(&owner, msg, 200, harness.clock.block_height)
        .unwrap();

    // Root changed from empty.
    assert_ne!(new_root, empty_queue_root());
    assert_eq!(operator.total_pending(), 1);
    assert_eq!(operator.inbox_root(&owner).unwrap(), new_root);
}

// ---------------------------------------------------------------------------
// Test 3: Owner drains inbox -> messages delivered with proofs
// ---------------------------------------------------------------------------
#[test]
fn owner_drains_inbox_with_proofs() {
    let mut harness = SimulationHarness::new_federation(3);

    let mut operator = well_bonded_operator();
    let owner = identity(0x01);
    operator.host_inbox(owner, 10, 50).unwrap();

    // Enqueue 3 messages from different senders.
    for i in 0u8..3 {
        harness.advance_blocks(1);
        let msg = test_msg(identity(i + 10), &[i; 16]);
        operator
            .receive_message(&owner, msg, 100 + i as u64 * 50, harness.clock.block_height)
            .unwrap();
    }
    assert_eq!(operator.total_pending(), 3);

    // Owner drains.
    harness.advance_blocks(10);
    let drained = operator.drain_for_owner(&owner, 100, harness.clock.block_height);
    assert_eq!(drained.len(), 3);

    // FIFO order verified.
    assert_eq!(drained[0].0.sender, identity(10));
    assert_eq!(drained[1].0.sender, identity(11));
    assert_eq!(drained[2].0.sender, identity(12));

    // All proofs valid.
    for (_, proof) in &drained {
        assert!(verify_dequeue_proof(proof));
    }

    // Queue is now empty.
    assert_eq!(operator.total_pending(), 0);
    assert_eq!(operator.inbox_root(&owner).unwrap(), empty_queue_root());
}

// ---------------------------------------------------------------------------
// Test 4: Operator GC: expired messages -> operator earns 10% fee
// ---------------------------------------------------------------------------
#[test]
fn gc_expired_operator_earns_10_percent_fee() {
    let mut harness = SimulationHarness::new_federation(3);

    let mut operator = well_bonded_operator();
    let owner = identity(0x01);
    operator.host_inbox(owner, 10, 50).unwrap();

    // Enqueue messages at height 5.
    harness.advance_blocks(5);
    let msg1 = test_msg(identity(0x10), b"will-expire-1");
    let msg2 = test_msg(identity(0x20), b"will-expire-2");
    operator
        .receive_message(&owner, msg1, 1000, harness.clock.block_height)
        .unwrap();
    operator
        .receive_message(&owner, msg2, 2000, harness.clock.block_height)
        .unwrap();

    assert_eq!(operator.total_pending(), 2);
    assert_eq!(operator.earned_fees, 0);

    // Advance well past TTL (TTL=20, current=30 > 5+20=25).
    let gc_result = operator.gc_expired(30, 20);

    assert_eq!(gc_result.messages_collected, 2);
    // Operator earns 10% of total deposits: (1000 + 2000) * 10% = 300.
    assert_eq!(gc_result.operator_fees, 300);
    assert_eq!(operator.earned_fees, 300);

    // Senders get 90% back.
    assert_eq!(gc_result.sender_refunds.len(), 2);
    assert_eq!(gc_result.sender_refunds[0].amount, 900); // 90% of 1000
    assert_eq!(gc_result.sender_refunds[0].sender, identity(0x10));
    assert_eq!(gc_result.sender_refunds[1].amount, 1800); // 90% of 2000
    assert_eq!(gc_result.sender_refunds[1].sender, identity(0x20));
}

// ---------------------------------------------------------------------------
// Test 5: Operator underbonded -> can't accept new inboxes
// ---------------------------------------------------------------------------
#[test]
fn underbonded_operator_rejects_new_inboxes() {
    let _harness = SimulationHarness::new_federation(3);

    // Bond = 500, rate = 100/unit. Can host max 5 capacity units.
    let mut operator = RelayOperator::new(identity(0xAA), 500, 50);

    // Host inbox with capacity 5 (requires 500 bond). OK.
    operator.host_inbox(identity(0x01), 5, 50).unwrap();
    assert!(!operator.is_underbonded());
    assert_eq!(operator.required_bond(), 500);

    // Try to host another inbox (even capacity 1 would need 600 total).
    let result = operator.host_inbox(identity(0x02), 1, 50);
    assert!(matches!(
        result,
        Err(RelayError::Underbonded {
            required: 600,
            actual: 500
        })
    ));

    // Operator still has 1 active inbox, not underbonded.
    assert_eq!(operator.active_inbox_count(), 1);
    assert!(!operator.is_underbonded());
}

// ---------------------------------------------------------------------------
// Test 6: Delivery dispute: sender proves enqueue, operator proves delivery -> vindicated
// ---------------------------------------------------------------------------
#[test]
fn delivery_dispute_operator_vindicated() {
    let mut harness = SimulationHarness::new_federation(3);

    let mut operator = well_bonded_operator();
    let owner = identity(0x01);
    operator.host_inbox(owner, 10, 50).unwrap();

    // Sender enqueues.
    harness.advance_blocks(10);
    let msg = test_msg(identity(0xBB), b"disputed-message");
    operator
        .receive_message(&owner, msg, 500, harness.clock.block_height)
        .unwrap();

    // Operator delivers (drains).
    harness.advance_blocks(5);
    let drained = operator.drain_for_owner(&owner, 1, harness.clock.block_height);
    assert_eq!(drained.len(), 1);
    let (entry, delivery_proof) = &drained[0];

    // Sender files dispute. Operator provides valid delivery proof.
    let dispute = DeliveryDispute {
        sender: identity(0xBB),
        message_hash: entry.content_hash,
        enqueue_proof: delivery_proof.clone(), // Reuse as enqueue proof structure
        claimed_delivery_height: Some(harness.clock.block_height),
        delivery_proof: Some(delivery_proof.clone()),
        filed_at: harness.clock.block_height + 1,
    };

    let outcome = operator.resolve_dispute(&dispute, harness.clock.block_height + 10);
    assert_eq!(outcome, DisputeOutcome::OperatorVindicated);
}

// ---------------------------------------------------------------------------
// Test 7: Delivery dispute: operator can't prove delivery -> slashed
// ---------------------------------------------------------------------------
#[test]
fn delivery_dispute_operator_slashed() {
    let mut harness = SimulationHarness::new_federation(3);

    let mut operator = well_bonded_operator();
    let owner = identity(0x01);
    operator.host_inbox(owner, 10, 50).unwrap();

    // Sender enqueues.
    harness.advance_blocks(10);
    let msg = test_msg(identity(0xBB), b"lost-message");
    operator
        .receive_message(&owner, msg, 500, harness.clock.block_height)
        .unwrap();

    // Drain to get a proof structure (simulating the enqueue receipt).
    let drained = operator.drain_for_owner(&owner, 1, harness.clock.block_height);
    let (entry, enqueue_proof) = &drained[0];

    // Sender files dispute. Operator has NO delivery proof.
    let filed_at = 20u64;
    let dispute = DeliveryDispute {
        sender: identity(0xBB),
        message_hash: entry.content_hash,
        enqueue_proof: enqueue_proof.clone(),
        claimed_delivery_height: None,
        delivery_proof: None,
        filed_at,
    };

    // Before SLA deadline (filed_at + max_delivery_latency = 20 + 50 = 70).
    // At height 69, still pending (returns InvalidDispute as "pending").
    let outcome = operator.resolve_dispute(&dispute, 69);
    assert_eq!(outcome, DisputeOutcome::InvalidDispute);

    // After SLA deadline: operator is slashed.
    let outcome = operator.resolve_dispute(&dispute, 75);
    assert_eq!(
        outcome,
        DisputeOutcome::OperatorSlashed {
            slash_amount: 100_000, // full bond / 1 active inbox
        }
    );
}

// ---------------------------------------------------------------------------
// Test 8: Operator goes offline: messages queue, owner reconnects later -> drain works
// ---------------------------------------------------------------------------
#[test]
fn operator_offline_messages_queue_reconnect_drain() {
    let mut harness = SimulationHarness::new_federation(3);

    let mut operator = well_bonded_operator();
    let owner = identity(0x01);
    operator.host_inbox(owner, 20, 50).unwrap();

    // Messages enqueued while owner is offline (simulated by not draining).
    for i in 0u8..5 {
        harness.advance_blocks(2);
        let msg = test_msg(identity(i + 10), &[i; 32]);
        operator
            .receive_message(&owner, msg, 150, harness.clock.block_height)
            .unwrap();
    }

    // All 5 messages buffered.
    assert_eq!(operator.total_pending(), 5);

    // Significant time passes (owner offline).
    harness.advance_blocks(100);

    // Owner reconnects and drains all.
    let drained = operator.drain_for_owner(&owner, 100, harness.clock.block_height);
    assert_eq!(drained.len(), 5);

    // Messages in order, all proofs valid.
    for i in 0u8..5 {
        assert_eq!(drained[i as usize].0.sender, identity(i + 10));
        assert!(verify_dequeue_proof(&drained[i as usize].1));
    }

    assert_eq!(operator.total_pending(), 0);
}

// ---------------------------------------------------------------------------
// Test 9 (bonus): Partial drain respects max parameter
// ---------------------------------------------------------------------------
#[test]
fn partial_drain_respects_max_parameter() {
    let mut harness = SimulationHarness::new_federation(3);

    let mut operator = well_bonded_operator();
    let owner = identity(0x01);
    operator.host_inbox(owner, 20, 50).unwrap();

    // Enqueue 8 messages.
    for i in 0u8..8 {
        harness.advance_blocks(1);
        let msg = test_msg(identity(i + 1), &[i; 8]);
        operator
            .receive_message(&owner, msg, 100, harness.clock.block_height)
            .unwrap();
    }

    // Drain only 3.
    let drained = operator.drain_for_owner(&owner, 3, harness.clock.block_height);
    assert_eq!(drained.len(), 3);
    assert_eq!(operator.total_pending(), 5);

    // Drain the remaining.
    let drained2 = operator.drain_for_owner(&owner, 100, harness.clock.block_height);
    assert_eq!(drained2.len(), 5);
    assert_eq!(operator.total_pending(), 0);
}

// ---------------------------------------------------------------------------
// Test 10 (bonus): Receive to evicted inbox fails
// ---------------------------------------------------------------------------
#[test]
fn receive_to_evicted_inbox_fails() {
    let mut harness = SimulationHarness::new_federation(3);

    let mut operator = well_bonded_operator();
    let owner = identity(0x01);
    operator.host_inbox(owner, 10, 50).unwrap();

    // Enqueue one message, then evict.
    harness.advance_blocks(1);
    let msg = test_msg(identity(0x10), b"before-eviction");
    operator
        .receive_message(&owner, msg, 100, harness.clock.block_height)
        .unwrap();
    operator.evict_inbox(&owner);

    // Trying to send to evicted inbox fails.
    let msg2 = test_msg(identity(0x20), b"after-eviction");
    let result = operator.receive_message(&owner, msg2, 100, harness.clock.block_height);
    assert!(matches!(result, Err(RelayError::InboxNotFound { .. })));
}
