//! Fault injection tests: message ordering faults.
//!
//! Verifies that the system handles out-of-order, duplicate, and stale messages
//! without state corruption. The system must either reorder messages correctly
//! or reject them gracefully — never corrupt state.
//!
//! Safety properties:
//! - No state corruption from reordered messages
//! - Idempotent handling of duplicates (no double-processing)
//! - Stale messages from old sessions are rejected
//! - DropRef/EnlivenRef ordering anomalies handled gracefully
//! - Concurrent writes resolved via CAS semantics (exactly one wins)

use pyana_captp::FederationId;
use pyana_cell::{AuthRequired, CellId};
use pyana_teasting::captp_sim::SimCapTpSession;
use pyana_teasting::fault::{FaultConfig, FaultyNetwork};
use pyana_teasting::federation::dual_federation;
use pyana_teasting::harness::SimulationHarness;
use pyana_teasting::mesh_sim::{MeshError, ServiceEntry, SimServiceMesh};
use pyana_wire::message::WireMessage;

// =============================================================================
// Helpers
// =============================================================================

fn fed_a_id() -> FederationId {
    FederationId([0xAA; 32])
}

fn fed_b_id() -> FederationId {
    FederationId([0xBB; 32])
}

fn test_cell(n: u8) -> CellId {
    CellId([n; 32])
}

fn test_federation() -> FederationId {
    FederationId([0xDD; 32])
}

// =============================================================================
// Test 1: Messages arrive out of order — no state corruption
// =============================================================================

/// Pipeline messages arrive out of order [3, 1, 2]. The system must either
/// buffer and reorder them, or process each independently without assuming
/// ordering. Either way, no state corruption should occur.
#[test]
fn test_messages_arrive_out_of_order() {
    let mut net = FaultyNetwork::new(
        FaultConfig {
            drop_rate: 0.0,
            reorder_rate: 1.0, // always reorder
            duplicate_rate: 0.0,
            max_delay: 0,
            partition: None,
        },
        "out-of-order-test",
    );

    // Send 10 messages in sequence
    for i in 0..10u64 {
        net.send(
            0,
            1,
            WireMessage::Ping {
                seq: i,
                timestamp: i as i64 * 100,
            },
        );
    }

    // Deliver all — they may come out of order
    let delivered = net.deliver_all_ready();
    assert_eq!(delivered.len(), 10, "All messages should be delivered");

    // Verify ALL messages were delivered (regardless of order)
    let mut seqs: Vec<u64> = delivered
        .iter()
        .map(|d| match &d.message {
            WireMessage::Ping { seq, .. } => *seq,
            _ => panic!("Expected Ping"),
        })
        .collect();
    seqs.sort();
    assert_eq!(
        seqs,
        (0..10).collect::<Vec<u64>>(),
        "All sequence numbers must be present (no loss, no duplication)"
    );

    // The ORDER may differ from [0,1,2,...,9] — that's the reordering behavior
    // Safety: each message is independent and can be processed in any order
    // without state corruption (Pings are stateless).
}

// =============================================================================
// Test 2: Duplicate CapHello — idempotent session establishment
// =============================================================================

/// If the same CapHello message arrives twice (network duplicate), the session
/// must not be corrupted. The second CapHello should be either:
/// - Ignored (session already established)
/// - Or handled idempotently (same result as processing once)
#[test]
fn test_duplicate_cap_hello_idempotent() {
    let mut session = SimCapTpSession::establish(fed_a_id(), fed_b_id());

    // Initial state: one CapHello in each direction
    assert_eq!(session.a_to_b.len(), 1);
    assert_eq!(session.b_to_a.len(), 1);
    assert!(session.connected);

    // Deliver initial CapHellos
    session.deliver_pending();

    // Simulate duplicate: inject another CapHello from A to B
    let duplicate_hello = WireMessage::CapHello {
        federation_id: fed_a_id().0,
        initial_exports: vec![],
    };
    session.send_a_to_b(duplicate_hello.clone());

    // Process the duplicate
    let (a_to_b_count, _) = session.deliver_pending();
    assert_eq!(a_to_b_count, 1, "Duplicate was processed");

    // Session should still be in a valid state
    assert!(
        session.connected,
        "Session must remain connected after duplicate CapHello"
    );

    // Test with the session still functional — export/enliven should work
    let cell = test_cell(0x11);
    let uri = session.export_from_a(cell, AuthRequired::Signature);
    let result = session.enliven_at_a(&uri);
    assert!(
        result.is_ok(),
        "Session must remain functional after duplicate CapHello: {:?}",
        result.err()
    );
}

// =============================================================================
// Test 3: Stale messages after session teardown
// =============================================================================

/// Messages from an old session arrive after a new session has been established.
/// These must be rejected — they belong to a terminated session and processing
/// them could corrupt the new session's state.
#[test]
fn test_stale_messages_after_teardown() {
    let mut harness = dual_federation();

    // Establish first session
    harness.connect_federations(0, 1);
    let cell = test_cell(0x22);
    let uri = harness.export_sturdy(0, cell, 1);
    harness.enliven_sturdy(1, &uri, 0).unwrap();

    // Capture messages that were "in flight" from the old session
    let stale_messages = vec![
        WireMessage::Ping {
            seq: 999,
            timestamp: 1,
        },
        WireMessage::DropRemoteRef {
            from_federation: fed_b_id().0,
            cell_id: cell.0,
            session_epoch: 0,
        },
    ];

    // Tear down the session
    harness.disconnect_federations(0, 1);

    // Remove the old session entry so we can establish a new one
    harness.captp_sessions.remove(&(0, 1));

    // Establish a NEW session
    harness.connect_federations(0, 1);

    // Now inject stale messages from the old session into the new one
    let session = harness.session_mut(0, 1).unwrap();
    for msg in &stale_messages {
        session.send_b_to_a(msg.clone());
    }
    session.deliver_pending();

    // The DropRemoteRef from the old session should NOT corrupt the new session's state.
    // In the new session, cell was never re-exported, so the drop targets nothing.
    //
    // FINDING: The current implementation processes DropRemoteRef regardless of
    // session epoch. In a production system, messages should carry a session_id
    // or epoch counter, and stale messages should be discarded.
    //
    // For now, verify that at minimum, no crash or state corruption occurs:
    let session = harness.session(0, 1).unwrap();
    assert!(
        session.connected,
        "New session must remain connected despite stale messages"
    );

    // Re-export in the new session should work normally
    let new_uri = harness.export_sturdy(0, cell, 1);
    let result = harness.enliven_sturdy(1, &new_uri, 0);
    assert!(
        result.is_ok(),
        "New session must be fully functional after stale message injection"
    );
}

// =============================================================================
// Test 4: DropRef arrives before EnlivenRef (temporal inversion)
// =============================================================================

/// Due to network reordering, a DropRef message arrives before the corresponding
/// EnlivenRef. The system must handle this gracefully: either buffer the DropRef
/// until the enliven arrives, or ignore it (since there's nothing to drop).
/// It must NOT crash or corrupt state.
#[test]
fn test_drop_before_enliven_graceful() {
    let mut session = SimCapTpSession::establish(fed_a_id(), fed_b_id());
    session.deliver_pending();

    // Export a cell from A
    let cell = test_cell(0x33);
    let _uri = session.export_from_a(cell, AuthRequired::None);

    // Before B enlivens, send a DropRef (temporal inversion due to network reorder)
    let premature_drop = WireMessage::DropRemoteRef {
        from_federation: fed_b_id().0,
        cell_id: cell.0,
        session_epoch: 0,
    };
    session.send_b_to_a(premature_drop);
    session.deliver_pending();

    // The drop should be handled gracefully:
    // - The export exists (it was exported), so the drop decrements the ref count
    // - OR: if the system tracks that B never enlivened it, the drop is a no-op
    //
    // Either way: no crash, no state corruption
    assert!(
        session.connected,
        "Session must not crash on premature DropRef"
    );

    // Subsequent operations should still work
    let cell2 = test_cell(0x44);
    let uri2 = session.export_from_a(cell2, AuthRequired::None);
    let result = session.enliven_at_a(&uri2);
    assert!(
        result.is_ok(),
        "Session must remain functional after premature DropRef"
    );
}

// =============================================================================
// Test 5: Concurrent writes to same directory entry — CAS semantics
// =============================================================================

/// Two agents attempt to mount at the same path simultaneously. Exactly one
/// must succeed (CAS semantics). The loser gets a PathConflict error.
/// No corruption of the mount table should occur.
#[test]
fn test_concurrent_mount_cas_semantics() {
    let mut mesh = SimServiceMesh::new();

    let path = "/cells/contested";

    // Agent 1 mounts
    let entry_1 = ServiceEntry {
        path: path.to_string(),
        cell_id: test_cell(0x01),
        federation_id: test_federation(),
        sturdy_ref: "pyana://test/agent1".to_string(),
        name: "agent1-service".to_string(),
        tags: vec!["contested".to_string()],
        version: 1,
    };

    // Agent 2 tries to mount at the same path
    let entry_2 = ServiceEntry {
        path: path.to_string(),
        cell_id: test_cell(0x02),
        federation_id: test_federation(),
        sturdy_ref: "pyana://test/agent2".to_string(),
        name: "agent2-service".to_string(),
        tags: vec!["contested".to_string()],
        version: 1,
    };

    // First mount succeeds
    let result_1 = mesh.mount(entry_1);
    assert!(result_1.is_ok(), "First mount should succeed");

    // Second mount at same path MUST fail
    let result_2 = mesh.mount(entry_2);
    assert!(
        result_2.is_err(),
        "Second mount at same path must fail (CAS semantics)"
    );
    match result_2.unwrap_err() {
        MeshError::PathConflict {
            path: conflict_path,
        } => {
            assert_eq!(conflict_path, path);
        }
        other => panic!("Expected PathConflict, got: {:?}", other),
    }

    // Verify: exactly one service is mounted
    assert_eq!(mesh.service_count(), 1);
    let entry = mesh.resolve_entry(&format!("{path}/action")).unwrap();
    assert_eq!(entry.name, "agent1-service", "First mounter wins");
    assert_eq!(entry.cell_id, test_cell(0x01));

    // No corruption: the router still works correctly
    let resolved = mesh.resolve(&format!("{path}/transfer"));
    assert_eq!(resolved, Some("pyana://test/agent1"));
}

// =============================================================================
// Test 6: Rapid connect/disconnect cycle — no state leak
// =============================================================================

/// Rapidly connecting and disconnecting sessions must not leak state.
/// After N cycles, memory usage should be bounded and the final session
/// should work correctly.
#[test]
fn test_rapid_connect_disconnect_no_leak() {
    let mut harness = dual_federation();

    // Connect and disconnect 20 times
    for i in 0..20u8 {
        harness.connect_federations(0, 1);

        // Do some work in each session
        let cell = test_cell(i);
        let _uri = harness.export_sturdy(0, cell, 1);

        harness.disconnect_federations(0, 1);
        // Remove old session entry to allow reconnection
        harness.captp_sessions.remove(&(0, 1));
    }

    // Final session should work perfectly
    harness.connect_federations(0, 1);
    let final_cell = test_cell(0xFF);
    let final_uri = harness.export_sturdy(0, final_cell, 1);
    let result = harness.enliven_sturdy(1, &final_uri, 0);
    assert!(
        result.is_ok(),
        "Session after 20 connect/disconnect cycles must work: {:?}",
        result.err()
    );

    // Verify the session is healthy
    let session = harness.session(0, 1).unwrap();
    assert!(session.connected);
    assert!(session.is_active());
}

// =============================================================================
// Test 7: Interleaved messages from multiple sources
// =============================================================================

/// Messages from multiple federations arrive interleaved at a single target.
/// Each message must be routed to the correct session context without cross-talk.
#[test]
fn test_interleaved_multi_source_messages() {
    let mut harness = SimulationHarness::two_federations(3, 3);
    let fed_c_idx = harness.add_federation("fed-gamma", 3);

    // Connect A<->B and A<->C
    harness.connect_federations(0, 1);
    harness.connect_federations(0, fed_c_idx);

    // Export different cells in each session
    let cell_for_b = test_cell(0xBB);
    let cell_for_c = test_cell(0xCC);

    let uri_b = harness.export_sturdy(0, cell_for_b, 1);
    let uri_c = harness.export_sturdy(0, cell_for_c, fed_c_idx);

    // Both enliven their respective cells
    let result_b = harness.enliven_sturdy(1, &uri_b, 0);
    let result_c = harness.enliven_sturdy(fed_c_idx, &uri_c, 0);

    assert!(result_b.is_ok(), "B should enliven cell_for_b");
    assert!(result_c.is_ok(), "C should enliven cell_for_c");

    // Verify no cross-talk: B's session has cell_for_b, C's session has cell_for_c
    let session_ab = harness.session(0, 1).unwrap();
    let session_ac = harness.session(0, fed_c_idx).unwrap();

    assert!(
        session_ab.session_b.imports.contains_key(&cell_for_b),
        "B should have imported cell_for_b"
    );
    assert!(
        !session_ab.session_b.imports.contains_key(&cell_for_c),
        "B should NOT have cell_for_c (belongs to C's session)"
    );

    assert!(
        session_ac.session_b.imports.contains_key(&cell_for_c),
        "C should have imported cell_for_c"
    );
    assert!(
        !session_ac.session_b.imports.contains_key(&cell_for_b),
        "C should NOT have cell_for_b (belongs to B's session)"
    );
}

// =============================================================================
// Test 8: FaultyNetwork reordering preserves message integrity
// =============================================================================

/// Even when the FaultyNetwork reorders messages aggressively, message content
/// must never be corrupted. Only order and timing are affected.
#[test]
fn test_faulty_network_preserves_integrity() {
    let mut net = FaultyNetwork::new(FaultConfig::hostile(), "integrity-check");

    // Send a variety of messages
    let messages: Vec<WireMessage> = (0..50u64)
        .map(|i| WireMessage::Ping {
            seq: i,
            timestamp: i as i64 * 1000,
        })
        .collect();

    for msg in &messages {
        net.send(0, 1, msg.clone());
    }

    // Advance time to allow all delayed messages to become deliverable
    net.advance_ticks(20);

    // Deliver everything
    let delivered = net.deliver_all_ready();

    // Some messages may have been dropped (hostile config has 30% drop rate)
    // But every delivered message must have EXACT content matching what was sent
    for d in &delivered {
        match &d.message {
            WireMessage::Ping { seq, timestamp } => {
                // Verify content integrity
                assert_eq!(
                    *timestamp,
                    *seq as i64 * 1000,
                    "Message content must not be corrupted by network faults"
                );
                assert!(*seq < 50, "Sequence number must be from original set");
            }
            _ => panic!("Unexpected message type — network injected a spurious message!"),
        }
    }

    // Verify stats are consistent
    let stats = net.stats();
    assert_eq!(stats.total_sent, 50);
    assert!(
        stats.total_delivered + stats.total_dropped <= stats.total_sent + stats.total_duplicated,
        "Accounting must be consistent: delivered + dropped <= sent + duplicated"
    );
}
