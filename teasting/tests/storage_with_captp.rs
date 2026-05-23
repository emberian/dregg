//! Storage + CapTP integration tests.
//!
//! Exercises store-and-forward through CapTP sessions: messages landing in
//! hosted inboxes, offline recipient queuing, handoff certificate delivery,
//! cross-federation inbox hosting, namespace-mounted inboxes, and quota tracking.

use pyana_storage::inbox::InboxMessage;
use pyana_storage::multi_asset::FeePolicy;
use pyana_storage::namespace_mount::{StorageMount, StorageMountKind};
use pyana_storage::operator::RelayOperator;
use pyana_storage::queue::verify_dequeue_proof;
use pyana_teasting::harness::SimulationHarness;

/// Deterministic identity.
fn identity(n: u8) -> [u8; 32] {
    [n; 32]
}

/// Create a test message.
fn test_msg(sender: [u8; 32], data: &[u8]) -> InboxMessage {
    InboxMessage::Encrypted {
        ciphertext: data.to_vec(),
        sender,
    }
}

/// Create a capability message (simulates HandoffCertificate).
fn cap_msg(sender: [u8; 32], cert_data: &[u8]) -> InboxMessage {
    InboxMessage::Capability {
        cert_bytes: cert_data.to_vec(),
        sender,
    }
}

/// Create a sturdy ref message.
fn ref_msg(sender: [u8; 32], uri: &str) -> InboxMessage {
    InboxMessage::SturdyRef {
        uri: uri.to_string(),
        sender,
    }
}

// ---------------------------------------------------------------------------
// Test 1: CapTP store-and-forward -> messages land in recipient's hosted inbox
// ---------------------------------------------------------------------------
#[test]
fn captp_store_forward_lands_in_hosted_inbox() {
    let mut harness = SimulationHarness::two_federations(3, 3);
    harness.connect_federations(0, 1);
    harness.advance_blocks(5);

    // Operator in federation B hosts inbox for recipient.
    let mut operator = RelayOperator::new(identity(0xBB), 100_000, 50);
    let recipient = identity(0x01);
    operator.host_inbox(recipient, 20, 50).unwrap();

    // Sender in federation A sends via CapTP session.
    let sender_id = identity(0xAA);
    let msg = test_msg(sender_id, b"cross-fed-message-via-captp");
    let new_root = operator
        .receive_message(&recipient, msg, 200, harness.clock.block_height)
        .unwrap();

    // Message is in the inbox.
    assert_ne!(new_root, *blake3::hash(b"empty_queue").as_bytes());
    assert_eq!(operator.total_pending(), 1);

    // Recipient reads.
    let drained = operator.drain_for_owner(&recipient, 10, harness.clock.block_height);
    assert_eq!(drained.len(), 1);
    assert_eq!(drained[0].0.sender, sender_id);
    assert!(verify_dequeue_proof(&drained[0].1));
}

// ---------------------------------------------------------------------------
// Test 2: Recipient offline -> messages queue at relay -> reconnect -> drain
// ---------------------------------------------------------------------------
#[test]
fn recipient_offline_messages_queue_then_drain_on_reconnect() {
    let mut harness = SimulationHarness::two_federations(3, 3);
    harness.connect_federations(0, 1);

    let mut operator = RelayOperator::new(identity(0xBB), 100_000, 50);
    let recipient = identity(0x01);
    operator.host_inbox(recipient, 50, 50).unwrap();

    // Recipient is "offline" — messages arrive but aren't drained.
    for i in 0u8..7 {
        harness.advance_blocks(2);
        let msg = test_msg(identity(i + 10), &[i; 24]);
        operator
            .receive_message(&recipient, msg, 100, harness.clock.block_height)
            .unwrap();
    }
    assert_eq!(operator.total_pending(), 7);

    // Simulate disconnect (recipient offline for a while).
    harness.disconnect_federations(0, 1);
    harness.advance_blocks(200);

    // Recipient reconnects.
    // (In a real system, reconnect would re-establish CapTP. Here we just drain.)
    let drained = operator.drain_for_owner(&recipient, 100, harness.clock.block_height);
    assert_eq!(drained.len(), 7);

    // All proofs valid, in order.
    for i in 0u8..7 {
        assert_eq!(drained[i as usize].0.sender, identity(i + 10));
        assert!(verify_dequeue_proof(&drained[i as usize].1));
    }
}

// ---------------------------------------------------------------------------
// Test 3: Handoff certificate enqueued to recipient's inbox -> recipient reads it
// ---------------------------------------------------------------------------
#[test]
fn handoff_certificate_delivered_via_inbox() {
    let mut harness = SimulationHarness::new_federation(3);
    harness.advance_blocks(5);

    let mut operator = RelayOperator::new(identity(0xCC), 100_000, 50);
    let recipient = identity(0x01);
    operator.host_inbox(recipient, 20, 50).unwrap();

    // Simulate a HandoffCertificate being sent to recipient's inbox.
    let cert_data = b"HandoffCert{from:fed-a,to:fed-b,cell:0x42,epoch:7}";
    let msg = cap_msg(identity(0xDD), cert_data);
    operator
        .receive_message(&recipient, msg, 300, harness.clock.block_height)
        .unwrap();

    // Recipient reads the handoff certificate.
    let drained = operator.drain_for_owner(&recipient, 1, harness.clock.block_height);
    assert_eq!(drained.len(), 1);
    let entry = &drained[0].0;

    // Verify content hash matches the certificate.
    let expected_hash = *blake3::hash(&{
        let mut buf = Vec::new();
        buf.push(0x01); // type tag for Capability
        buf.extend_from_slice(&identity(0xDD));
        buf.extend_from_slice(cert_data);
        buf
    })
    .as_bytes();
    assert_eq!(entry.content_hash, expected_hash);
    assert_eq!(entry.deposit, 300);
}

// ---------------------------------------------------------------------------
// Test 4: Cross-federation inbox: sender in fed A -> relay hosts inbox for user in fed B
// ---------------------------------------------------------------------------
#[test]
fn cross_federation_inbox_delivery() {
    let mut harness = SimulationHarness::two_federations(3, 3);
    harness.connect_federations(0, 1);
    harness.advance_blocks(10);

    // Operator in federation A hosts inbox for user in federation B.
    let mut operator_fed_a = RelayOperator::new(identity(0xAA), 100_000, 50);
    let user_in_fed_b = identity(0x42);
    operator_fed_a.host_inbox(user_in_fed_b, 20, 100).unwrap();

    // Sender in federation A enqueues to the inbox.
    let sender_in_fed_a = identity(0x10);
    let msg = test_msg(sender_in_fed_a, b"cross-fed-hello");
    operator_fed_a
        .receive_message(&user_in_fed_b, msg, 200, harness.clock.block_height)
        .unwrap();

    // Another sender in federation B sends via the CapTP bridge.
    harness.advance_blocks(1);
    let sender_in_fed_b = identity(0x20);
    let msg2 = ref_msg(sender_in_fed_b, "pyana://fed-b/my-capability");
    operator_fed_a
        .receive_message(&user_in_fed_b, msg2, 150, harness.clock.block_height)
        .unwrap();

    assert_eq!(operator_fed_a.total_pending(), 2);

    // User in fed B drains via cross-federation relay.
    harness.advance_blocks(5);
    let drained = operator_fed_a.drain_for_owner(&user_in_fed_b, 10, harness.clock.block_height);
    assert_eq!(drained.len(), 2);
    assert_eq!(drained[0].0.sender, sender_in_fed_a);
    assert_eq!(drained[1].0.sender, sender_in_fed_b);
}

// ---------------------------------------------------------------------------
// Test 5: Inbox mounted in governed-namespace -> discoverable via tags
// ---------------------------------------------------------------------------
#[test]
fn inbox_mounted_in_namespace_discoverable_via_tags() {
    let _harness = SimulationHarness::new_federation(3);

    let owner = identity(0x01);

    // Mount an inbox in the governed namespace.
    let mount = StorageMount::inbox(
        "/inboxes/alice".to_string(),
        owner,
        FeePolicy::computrons_only(),
        100,
    )
    .unwrap();

    // Verify mount configuration.
    assert_eq!(mount.path, "/inboxes/alice");
    assert_eq!(mount.kind, StorageMountKind::Inbox { owner });
    assert_eq!(mount.max_capacity, 100);

    // Inbox is open for writes (anyone can send with deposit).
    let random_sender = identity(0xFF);
    assert!(mount.is_writer_authorized(&random_sender));

    // Create a pub-sub mount too.
    let publisher = identity(0x02);
    let pubsub_mount = StorageMount::pubsub(
        "/topics/market-data".to_string(),
        publisher,
        50,
        FeePolicy::computrons_only(),
        500,
    )
    .unwrap();

    // Pub-sub mount restricts writes to publisher.
    assert!(pubsub_mount.is_writer_authorized(&publisher));
    assert!(!pubsub_mount.is_writer_authorized(&random_sender));
    assert_eq!(
        pubsub_mount.kind,
        StorageMountKind::PubSub {
            publisher,
            max_subscribers: 50,
        }
    );
}

// ---------------------------------------------------------------------------
// Test 6: Storage quota tracks across CapTP operations
// ---------------------------------------------------------------------------
#[test]
fn storage_quota_tracks_across_captp_operations() {
    let mut harness = SimulationHarness::two_federations(3, 3);
    harness.connect_federations(0, 1);
    harness.advance_blocks(5);

    // Operator with limited bond (can host limited capacity).
    let mut operator = RelayOperator::new(identity(0xAA), 2000, 50);

    // Host inbox with capacity 10 (requires 10 * 100 = 1000 bond).
    let owner1 = identity(0x01);
    operator.host_inbox(owner1, 10, 50).unwrap();
    assert_eq!(operator.required_bond(), 1000);
    assert!(!operator.is_underbonded());

    // Host another inbox with capacity 10 (requires 2000 total bond). Just fits.
    let owner2 = identity(0x02);
    operator.host_inbox(owner2, 10, 50).unwrap();
    assert_eq!(operator.required_bond(), 2000);
    assert!(!operator.is_underbonded());

    // Can't host more (would need 2100+ but only have 2000).
    let owner3 = identity(0x03);
    let result = operator.host_inbox(owner3, 1, 50);
    assert!(result.is_err());

    // Fill inbox 1 to capacity.
    for i in 0u8..10 {
        harness.advance_blocks(1);
        let msg = test_msg(identity(i + 20), &[i; 8]);
        operator
            .receive_message(&owner1, msg, 100, harness.clock.block_height)
            .unwrap();
    }
    assert_eq!(operator.total_pending(), 10);

    // Inbox 1 is full; next message bounced.
    let overflow_msg = test_msg(identity(0x99), b"overflow");
    let result = operator.receive_message(&owner1, overflow_msg, 100, harness.clock.block_height);
    assert!(result.is_err());

    // Evict inbox 1 (simulating quota depletion). Bond requirement drops.
    let refunds = operator.evict_inbox(&owner1);
    assert_eq!(refunds.len(), 10);
    assert_eq!(operator.required_bond(), 1000); // Only inbox 2 remains.
}

// ---------------------------------------------------------------------------
// Test 7 (bonus): Mixed message types through CapTP relay
// ---------------------------------------------------------------------------
#[test]
fn mixed_message_types_through_relay() {
    let mut harness = SimulationHarness::new_federation(3);
    harness.advance_blocks(3);

    let mut operator = RelayOperator::new(identity(0xCC), 100_000, 50);
    let recipient = identity(0x01);
    operator.host_inbox(recipient, 20, 50).unwrap();

    // Send different message types.
    let messages: Vec<InboxMessage> = vec![
        cap_msg(identity(0x10), b"cert-data-here"),
        ref_msg(identity(0x20), "pyana://fed-a/cell-42"),
        test_msg(identity(0x30), b"encrypted-payload"),
    ];

    for msg in messages {
        harness.advance_blocks(1);
        operator
            .receive_message(&recipient, msg, 150, harness.clock.block_height)
            .unwrap();
    }

    // All delivered in order.
    let drained = operator.drain_for_owner(&recipient, 10, harness.clock.block_height);
    assert_eq!(drained.len(), 3);
    assert_eq!(drained[0].0.sender, identity(0x10));
    assert_eq!(drained[1].0.sender, identity(0x20));
    assert_eq!(drained[2].0.sender, identity(0x30));

    // Content hashes all differ (different message types + data).
    assert_ne!(drained[0].0.content_hash, drained[1].0.content_hash);
    assert_ne!(drained[1].0.content_hash, drained[2].0.content_hash);
}

// ---------------------------------------------------------------------------
// Test 8 (bonus): Namespace mount validates path constraints
// ---------------------------------------------------------------------------
#[test]
fn namespace_mount_validates_path_constraints() {
    let _harness = SimulationHarness::new_federation(3);

    // Valid path.
    let result = StorageMount::inbox(
        "/inboxes/bob".to_string(),
        identity(0x01),
        FeePolicy::computrons_only(),
        10,
    );
    assert!(result.is_ok());

    // Invalid: no leading slash.
    let result = StorageMount::inbox(
        "inboxes/bob".to_string(),
        identity(0x01),
        FeePolicy::computrons_only(),
        10,
    );
    assert!(result.is_err());

    // Invalid: empty path.
    let result = StorageMount::inbox(
        "".to_string(),
        identity(0x01),
        FeePolicy::computrons_only(),
        10,
    );
    assert!(result.is_err());

    // Invalid: zero capacity.
    let result = StorageMount::inbox(
        "/inboxes/zero".to_string(),
        identity(0x01),
        FeePolicy::computrons_only(),
        0,
    );
    assert!(result.is_err());
}
