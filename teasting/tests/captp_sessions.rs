//! CapTP session lifecycle integration tests.
//!
//! Tests the full CapTP protocol flow across federation boundaries:
//! - Session establishment (CapHello exchange)
//! - Sturdy ref export, URI sharing, and enliven
//! - Distributed GC: drop refs trigger export count decrement
//! - Promise pipelining: batched actions resolve in sequence
//! - Handoff: offline capability transfer to third parties
//! - Store-and-forward: encrypted message queueing during offline periods

use pyana_captp::session::CapSession;
use pyana_captp::store_forward::{
    MessagePriority, MessageRelay, RelayInfo, StoreForwardClient, generate_x25519_keypair,
};
use pyana_captp::sturdy::SwissTable;
use pyana_captp::uri::PyanaUri;
use pyana_captp::{
    DropResult, ExportGcManager, FederationId, HandoffCertificate, HandoffPresentation,
    ImportGcManager, PipelineRegistry, PipelinedAction, validate_handoff,
};
use pyana_cell::AuthRequired;
use pyana_teasting::federation::dual_federation;
use pyana_teasting::harness::SimulationHarness;
use pyana_types::{CellId, generate_keypair};

// =============================================================================
// Helpers
// =============================================================================

fn fed_a_id() -> FederationId {
    FederationId([0xAA; 32])
}

fn fed_b_id() -> FederationId {
    FederationId([0xBB; 32])
}

fn test_cell(byte: u8) -> CellId {
    CellId([byte; 32])
}

fn make_action(method: &str) -> PipelinedAction {
    PipelinedAction {
        method: method.to_string(),
        args: vec![],
        authorization: vec![],
    }
}

// =============================================================================
// Test 1: Two federations establish a CapTP session (CapHello exchange)
// =============================================================================

/// Simulate a CapTP session establishment between two federations.
///
/// In the real protocol, CapHello messages carry identity + ephemeral keys.
/// Here we simulate the outcome: both sides create CapSession objects pointing
/// at each other, with consistent peer_id fields.
#[test]
fn test_captp_session_establishment() {
    let mut harness = dual_federation();

    // Federation A creates a session tracking federation B as peer.
    let mut session_a = CapSession::new(fed_b_id().0);
    // Federation B creates a session tracking federation A as peer.
    let mut session_b = CapSession::new(fed_a_id().0);

    // Initially neither session is active (no imports/exports).
    assert!(!session_a.is_active());
    assert!(!session_b.is_active());

    // After CapHello exchange, A exports a capability to B.
    let exported_cell = test_cell(0x11);
    session_a.export(exported_cell, AuthRequired::Signature);

    // B records the import from A.
    session_b.import(exported_cell, AuthRequired::Signature);

    // Both sessions are now active.
    assert!(session_a.is_active());
    assert!(session_b.is_active());

    // The export reference count on A is 1.
    assert_eq!(session_a.exports[&exported_cell].ref_count, 1);

    // Run consensus to confirm the sessions coexist with federation operations.
    harness.run_consensus_round(0);
    harness.run_consensus_round(1);
    harness.advance_blocks(1);
    harness.assert_all_nodes_agree(0);
    harness.assert_all_nodes_agree(1);
}

// =============================================================================
// Test 2: Export sturdy ref from Fed A -> share URI -> enliven from Fed B
// =============================================================================

/// Full sturdy ref lifecycle: export, URI construction, parsing, enliven.
#[test]
fn test_export_and_enliven_sturdy_ref() {
    let mut harness = dual_federation();

    let target_cell = test_cell(0x22);
    let federation_id = fed_a_id().0;

    // --- Fed A: export a cell as a sturdy reference ---
    let mut swiss_table = SwissTable::new();
    let swiss = swiss_table.export(target_cell, AuthRequired::Signature, 100, None);

    // Construct the shareable URI.
    let uri = swiss_table.make_uri(federation_id, &swiss).unwrap();
    let uri_string = uri.to_uri_string();
    assert!(uri_string.starts_with("pyana://"));

    // --- Transit: URI travels out-of-band to Fed B ---

    // --- Fed B: parse the URI and enliven ---
    let parsed_uri = PyanaUri::parse(&uri_string).unwrap();
    assert_eq!(parsed_uri.federation_id, federation_id);
    assert_eq!(parsed_uri.cell_id, target_cell.0);
    assert_eq!(parsed_uri.swiss, swiss);

    // Fed B presents the swiss number to Fed A's swiss table.
    let entry = swiss_table.enliven(&parsed_uri.swiss, 110).unwrap();
    assert_eq!(entry.cell_id, target_cell);
    assert_eq!(entry.permissions, AuthRequired::Signature);
    assert_eq!(entry.use_count, 1);

    harness.advance_blocks(1);
}

// =============================================================================
// Test 3: GC - Fed B drops ref -> Fed A's export count decrements
// =============================================================================

/// Distributed GC: when B drops a reference, A's export entry refcount decrements.
/// At zero refs, the export can be revoked.
#[test]
fn test_gc_drop_ref_decrements_export() {
    let mut harness = dual_federation();

    let cell = test_cell(0x33);
    let mut gc_a = ExportGcManager::new();
    let mut gc_b = ImportGcManager::new();

    // Fed A exports a cell to Fed B.
    gc_a.record_export(cell, fed_b_id(), 100);
    assert_eq!(gc_a.get(&cell).unwrap().total_refs, 1);

    // Fed B records the import.
    gc_b.record_import(fed_b_id(), cell);
    assert_eq!(gc_b.get(&fed_b_id(), &cell).unwrap().local_refs, 1);

    // Fed B drops the reference.
    let drop_msg = gc_b.local_ref_dropped(fed_b_id(), cell);
    assert!(drop_msg.is_some(), "Should generate a DropRef message");

    let msg = drop_msg.unwrap();
    assert_eq!(msg.target_federation, fed_b_id());
    assert_eq!(msg.cell_id, cell);

    // Fed A processes the drop.
    let result = gc_a.process_drop(cell, fed_b_id());
    assert_eq!(result, DropResult::CanRevoke);
    assert_eq!(gc_a.get(&cell).unwrap().total_refs, 0);

    // GC sweep removes the dead export.
    let swept = gc_a.gc_sweep();
    assert_eq!(swept.len(), 1);
    assert!(swept.contains(&cell));
    assert!(gc_a.is_empty());

    harness.advance_blocks(1);
}

// =============================================================================
// Test 4: Pipeline - Fed B sends 3 pipelined actions to Fed A, all resolve
// =============================================================================

/// Promise pipelining: three actions are batched as a chain. Resolving the
/// initial promise cascades delivery through all three steps.
#[test]
fn test_pipeline_three_actions_resolve() {
    let _harness = dual_federation();

    let mut registry = PipelineRegistry::new();
    let initial_promise = registry.create_promise();

    // Fed B pipelines 3 actions targeting the initial promise.
    let steps = vec![
        make_action("get_balance"),
        make_action("compute_fee"),
        make_action("execute_transfer"),
    ];

    let final_promise = registry
        .pipeline_chain(initial_promise, steps, fed_b_id())
        .unwrap();

    // All 4 promises exist (initial + 3 intermediate).
    assert_eq!(registry.promise_count(), 4);

    // Resolve the initial promise with a concrete cell.
    let step1_msgs = registry.resolve_promise(initial_promise, test_cell(0x01));
    assert_eq!(step1_msgs.len(), 1);
    assert_eq!(step1_msgs[0].action.method, "get_balance");

    // Resolve step 1's result.
    let step1_result = step1_msgs[0].result_promise_id.unwrap();
    let step2_msgs = registry.resolve_promise(step1_result, test_cell(0x02));
    assert_eq!(step2_msgs.len(), 1);
    assert_eq!(step2_msgs[0].action.method, "compute_fee");

    // Resolve step 2's result.
    let step2_result = step2_msgs[0].result_promise_id.unwrap();
    let step3_msgs = registry.resolve_promise(step2_result, test_cell(0x03));
    assert_eq!(step3_msgs.len(), 1);
    assert_eq!(step3_msgs[0].action.method, "execute_transfer");

    // Step 3's result is the final promise.
    assert_eq!(step3_msgs[0].result_promise_id, Some(final_promise));

    // Resolve the final promise.
    let final_cell = test_cell(0x04);
    let delivered = registry.resolve_promise(final_promise, final_cell);
    assert!(delivered.is_empty(), "No further messages queued");

    // Verify final promise is fulfilled.
    assert!(matches!(
        registry.promise_state(final_promise),
        Some(pyana_captp::PipelinePromiseState::Fulfilled { resolved_cell }) if *resolved_cell == final_cell
    ));
}

// =============================================================================
// Test 5: Handoff - Fed A creates cert -> Fed C presents to Fed A -> gets access
// =============================================================================

/// Handoff protocol: A introduces C to a capability at A's target federation.
/// C presents the signed certificate and gains access.
#[test]
fn test_handoff_certificate_flow() {
    let _harness = SimulationHarness::two_federations(3, 3);

    // Setup identities.
    let (intro_sk, intro_pk) = generate_keypair();
    let intro_fed = FederationId(intro_pk.0);

    let (recip_sk, recip_pk) = generate_keypair();

    let target_fed = fed_a_id();
    let target_cell = test_cell(0x55);

    // Step 1: Introducer registers a swiss entry at the target.
    let mut swiss_table = SwissTable::new();
    let swiss = swiss_table.export(target_cell, AuthRequired::Signature, 100, None);

    // Step 2: Introducer creates the handoff certificate.
    let cert = HandoffCertificate::create(
        &intro_sk,
        intro_fed,
        target_fed,
        target_cell,
        recip_pk.0,
        AuthRequired::Signature,
        None,
        None,
        None,
        swiss,
    );

    // Verify the certificate signature.
    assert!(cert.verify_signature(&intro_pk));

    // Step 3: Recipient presents the certificate.
    let presentation = HandoffPresentation::create(cert, &recip_sk);
    assert!(presentation.verify_recipient_signature());

    // Step 4: Target validates the handoff.
    let known_federations = vec![intro_fed];
    let acceptance = validate_handoff(
        &presentation,
        &intro_pk,
        &mut swiss_table,
        &known_federations,
        150,
    )
    .unwrap();

    // Verify the acceptance grants access to the target cell.
    assert_eq!(acceptance.cell_id, target_cell);
    assert_eq!(acceptance.permissions, AuthRequired::Signature);
    assert_ne!(acceptance.routing_token, [0u8; 32]); // Non-zero routing token
}

// =============================================================================
// Test 6: Store-and-forward - queue messages while offline -> deliver on reconnect
// =============================================================================

/// Store-and-forward: messages are encrypted and queued when the destination
/// is offline. Upon reconnect, the destination drains its queue and decrypts
/// messages in causal order.
#[test]
fn test_store_and_forward_offline_delivery() {
    let mut harness = dual_federation();

    // Generate X25519 keys for Alice (Fed A) and Bob (Fed B).
    let (alice_secret, _alice_public) = generate_x25519_keypair();
    let (bob_secret, bob_public) = generate_x25519_keypair();

    // Alice prepares messages for Bob while Bob is offline.
    let relay_info = RelayInfo {
        federation_id: FederationId([0xDD; 32]),
        endpoint: "relay.test.local".into(),
        capacity: 1000,
    };
    let mut alice_client = StoreForwardClient::new(fed_a_id(), vec![relay_info]);
    let mut relay = MessageRelay::new(100, 1000);

    // Alice sends 3 messages while Bob is offline.
    let payloads = vec![
        b"captp:export cell_0x11".to_vec(),
        b"captp:invoke method_a".to_vec(),
        b"captp:invoke method_b".to_vec(),
    ];

    for payload in &payloads {
        let msg = alice_client.prepare_message(
            fed_b_id(),
            payload,
            &bob_public,
            &alice_secret,
            MessagePriority::Normal,
            100, // TTL: 100 blocks
            harness.clock.block_height,
        );
        alice_client.queue_on_relay(msg, &mut relay);
    }

    // Verify relay has 3 pending messages for Bob.
    assert_eq!(relay.pending_count(&fed_b_id()), 3);
    assert_eq!(alice_client.unacknowledged_count(), 3);

    // Simulate Bob coming online: drain the relay.
    harness.advance_blocks(5); // Some time passes.

    let drained = relay.drain(&fed_b_id());
    assert_eq!(drained.len(), 3);

    // Bob decrypts messages in causal order.
    let results = StoreForwardClient::process_incoming(drained, &bob_secret).unwrap();
    assert_eq!(results.len(), 3);
    assert_eq!(results[0], (0, payloads[0].clone()));
    assert_eq!(results[1], (1, payloads[1].clone()));
    assert_eq!(results[2], (2, payloads[2].clone()));

    // Relay is now empty.
    assert_eq!(relay.pending_count(&fed_b_id()), 0);
    assert_eq!(relay.total_stored(), 0);

    // Acknowledge messages.
    for i in 0..3u64 {
        alice_client.acknowledge(&fed_b_id(), i);
    }
    assert_eq!(alice_client.unacknowledged_count(), 0);

    harness.advance_blocks(1);
    harness.assert_all_nodes_agree(0);
    harness.assert_all_nodes_agree(1);
}

// =============================================================================
// Test 7: Store-and-forward TTL expiry
// =============================================================================

/// Messages that exceed their TTL are expired by the relay and never delivered.
#[test]
fn test_store_forward_ttl_expiry() {
    let mut harness = dual_federation();

    let (alice_secret, _alice_public) = generate_x25519_keypair();
    let (_bob_secret, bob_public) = generate_x25519_keypair();

    let mut alice_client = StoreForwardClient::new(fed_a_id(), vec![]);
    let mut relay = MessageRelay::new(100, 1000);

    // Alice sends a message with TTL=10 blocks.
    let msg = alice_client.prepare_message(
        fed_b_id(),
        b"time-sensitive action",
        &bob_public,
        &alice_secret,
        MessagePriority::High,
        10,  // TTL: 10 blocks
        100, // queued at height 100
    );
    relay.enqueue(msg).unwrap();
    assert_eq!(relay.pending_count(&fed_b_id()), 1);

    // Advance past TTL (height 100 + 10 = 110).
    harness.advance_blocks(12);

    // Expire stale messages.
    let expired = relay.expire(110);
    assert_eq!(expired, 1);
    assert_eq!(relay.pending_count(&fed_b_id()), 0);

    // Bob comes online too late: no messages waiting.
    let drained = relay.drain(&fed_b_id());
    assert!(drained.is_empty());
}

// =============================================================================
// Test 8: Multiple exports from A, partial GC from B
// =============================================================================

/// Multiple capabilities exported to B. B drops some but not all. Export GC
/// only revokes entries that reach zero refs.
#[test]
fn test_partial_gc_multiple_exports() {
    let _harness = dual_federation();

    let mut gc_a = ExportGcManager::new();

    let cell_1 = test_cell(0x41);
    let cell_2 = test_cell(0x42);
    let cell_3 = test_cell(0x43);

    // Export all three to Fed B.
    gc_a.record_export(cell_1, fed_b_id(), 100);
    gc_a.record_export(cell_2, fed_b_id(), 101);
    gc_a.record_export(cell_3, fed_b_id(), 102);
    assert_eq!(gc_a.len(), 3);

    // B drops cell_1 and cell_3 but keeps cell_2.
    let r1 = gc_a.process_drop(cell_1, fed_b_id());
    assert_eq!(r1, DropResult::CanRevoke);

    let r3 = gc_a.process_drop(cell_3, fed_b_id());
    assert_eq!(r3, DropResult::CanRevoke);

    // Sweep dead entries.
    let swept = gc_a.gc_sweep();
    assert_eq!(swept.len(), 2);
    assert!(swept.contains(&cell_1));
    assert!(swept.contains(&cell_3));

    // cell_2 is still held.
    assert_eq!(gc_a.len(), 1);
    assert!(gc_a.get(&cell_2).is_some());
    assert_eq!(gc_a.get(&cell_2).unwrap().total_refs, 1);
}
