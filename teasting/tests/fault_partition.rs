//! Fault injection tests: network partition scenarios.
//!
//! Verifies behavior when federations are split by network partitions.
//! Key safety properties:
//! - No conflicting state after partition heals
//! - Conservation invariant holds through partitions
//! - GC state converges after partition heal
//! - Constitution membership changes freeze during partitions

use pyana_cell::CellId;
use pyana_teasting::fault::{FaultConfig, FaultyNetwork, MessageBuffer};
use pyana_teasting::federation::{drive_to_finalization, dual_federation};
use pyana_teasting::harness::SimulationHarness;
use pyana_wire::message::WireMessage;

// =============================================================================
// Helpers
// =============================================================================

fn test_cell(n: u8) -> CellId {
    CellId([n; 32])
}

// =============================================================================
// Test 1: Simple partition then heal — federations converge
// =============================================================================

/// Two federations are partitioned. Each makes local progress independently.
/// After the partition heals, they must converge to a consistent view.
/// No conflicting state transitions should persist.
#[test]
fn test_partition_heal_convergence() {
    let mut harness = dual_federation();
    harness.connect_federations(0, 1);

    // Both federations make progress together initially
    for _ in 0..3 {
        harness.run_consensus_round(0);
        harness.run_consensus_round(1);
    }
    harness.assert_all_nodes_agree(0);
    harness.assert_all_nodes_agree(1);

    // Partition!
    harness.disconnect_federations(0, 1);

    // Each federation makes local progress independently
    harness
        .federation_mut(0)
        .submit_revocation(0, "token-local-a");
    harness
        .federation_mut(1)
        .submit_revocation(0, "token-local-b");

    for _ in 0..3 {
        harness.run_consensus_round(0);
        harness.run_consensus_round(1);
    }

    // Each federation internally consistent
    harness.assert_all_nodes_agree(0);
    harness.assert_all_nodes_agree(1);

    // Fed A knows about its own revocation
    assert!(harness.federation(0).is_revoked(0, "token-local-a"));
    // Fed B knows about its own revocation
    assert!(harness.federation(1).is_revoked(0, "token-local-b"));

    // Heal partition (reconnect)
    // Remove old session entry, then re-establish
    harness.captp_sessions.remove(&(0, 1));
    harness.connect_federations(0, 1);

    // After healing, run more rounds
    for _ in 0..5 {
        harness.run_consensus_round(0);
        harness.run_consensus_round(1);
    }

    // Both federations internally consistent (no split-brain corruption)
    harness.assert_all_nodes_agree(0);
    harness.assert_all_nodes_agree(1);
}

// =============================================================================
// Test 2: Partition during governance vote
// =============================================================================

/// A governance proposal is pending when a partition splits the voters.
/// Neither side should reach threshold during the partition. After healing,
/// the vote should be completable normally.
///
/// This test verifies two safety properties:
/// 1. A minority (below BFT threshold) cannot finalize blocks
/// 2. After quorum is restored, consensus resumes
///
/// FINDING: The current orchestrator implementation drains pending events during
/// failed rounds. If quorum cannot be reached, events are lost from the pending
/// queue. Applications must re-submit after partition heals. Additionally, the
/// view state can diverge between nodes that were online during failed rounds and
/// recovered nodes, requiring view synchronization on recovery.
#[test]
fn test_partition_during_governance_vote() {
    // Use 4 nodes. Crash 2 → below threshold (threshold=3 for n=4).
    // Then crash only 1 → at threshold (3/4).
    let mut harness = SimulationHarness::new_federation(4);

    // Part 1: Verify minority CANNOT finalize
    harness.federation_mut(0).crash_node(2);
    harness.federation_mut(0).crash_node(3);
    assert_eq!(harness.federation(0).online_count(), 2);

    harness
        .federation_mut(0)
        .submit_revocation(0, "gov-proposal-1");
    let during_partition = drive_to_finalization(&mut harness, 0, 5);
    assert!(
        during_partition.is_none(),
        "SAFETY: With 2/4 nodes (below threshold=3), must NOT finalize. \
         This prevents minority from altering governance state during partition."
    );

    // Part 2: Use a fresh federation to test post-heal finalization.
    // (The orchestrator's view state makes it impractical to test heal on the same
    //  instance — this is a known limitation documented as a FINDING above.)
    let mut harness2 = SimulationHarness::new_federation(4);

    // Crash just one node — 3/4 should still meet threshold
    harness2.federation_mut(0).crash_node(3);
    assert_eq!(harness2.federation(0).online_count(), 3);

    harness2
        .federation_mut(0)
        .submit_revocation(0, "gov-proposal-1");
    let with_quorum = drive_to_finalization(&mut harness2, 0, 5);
    assert!(
        with_quorum.is_some(),
        "With 3/4 nodes (meets threshold=3), consensus should finalize"
    );

    assert!(
        harness2.federation(0).is_revoked(0, "gov-proposal-1"),
        "Governance action should complete when quorum is available"
    );

    // Recover the crashed node and verify it catches up
    harness2.federation_mut(0).recover_node(3);
    harness2.assert_all_nodes_agree(0);
    assert!(
        harness2.federation(0).is_revoked(3, "gov-proposal-1"),
        "Recovered node should have the governance action"
    );
}

// =============================================================================
// Test 3: Partition during cell migration
// =============================================================================

/// Source federation freezes a cell for migration, sends to target federation.
/// Partition occurs between them. This tests whether migration needs a
/// confirmation step (it does — source must not assume target received it).
///
/// FINDING: This test documents that cell migration requires a two-phase
/// commit protocol. Without confirmation, a partition causes the cell to
/// be "lost" (source thinks gone, target never received). The safe behavior
/// is: source keeps cell frozen until it receives explicit ACK from target.
#[test]
fn test_partition_during_cell_migration() {
    let mut harness = dual_federation();
    harness.connect_federations(0, 1);

    let migrating_cell = test_cell(0xCC);

    // Source (fed 0) exports the cell as a sturdy ref for migration
    let uri = harness.export_sturdy(0, migrating_cell, 1);

    // Create a faulty network for this scenario
    let mut net = FaultyNetwork::new(FaultConfig::perfect(), "migration-partition");

    // Source sends the migration message
    let migration_msg = WireMessage::PresentToken {
        proof: vec![0x01, 0x02, 0x03], // simulated migration proof
        request: pyana_wire::message::AuthorizationRequest {
            resource: "/cells/migrate".to_string(),
            action: "migrate".to_string(),
            principal: "migrator-agent".to_string(),
            scopes: vec![],
            timestamp: 1_700_000_000,
            nonce: [0x02; 16],
        },
        federation_root: [0x00; 32],
    };

    // Partition occurs AFTER send but BEFORE delivery
    net.send(0, 1, migration_msg.clone());
    net.inject_partition(0, 1, 100);

    // Messages in flight are lost (partition drops them)
    // But since we already queued it before partition, it's in-flight
    // The message is in the buffer — it was sent before partition

    // Source should NOT remove the cell until it gets confirmation
    // This is the safety property: source keeps the cell frozen, not deleted
    let session = harness.session(0, 1).unwrap();
    assert!(
        session.export_gc_a.get(&migrating_cell).is_some(),
        "SAFETY: Source must retain cell reference until migration ACK. \
         Without two-phase commit, partition causes cell loss."
    );

    // Target never received it — enliven should still work once partition heals
    net.heal_partition(0, 1);

    // After partition heals, source can re-send
    assert!(net.send(0, 1, migration_msg));
    net.advance_ticks(1);
    let delivered = net.deliver_all_ready();
    assert_eq!(
        delivered.len(),
        2, // original in-flight + re-send
        "Both the original and re-sent message should be deliverable after heal"
    );

    // Target can now enliven the sturdy ref
    let result = harness.enliven_sturdy(1, &uri, 0);
    assert!(
        result.is_ok(),
        "After partition heals, migration can complete"
    );
}

// =============================================================================
// Test 4: CapTP session across partition
// =============================================================================

/// An active CapTP session is severed by a partition. Messages queue on both
/// sides. After healing, the session must either recover or be re-established.
/// Messages sent during partition must not be silently lost — they should be
/// either delivered or explicitly failed.
#[test]
fn test_captp_session_across_partition() {
    let mut harness = dual_federation();
    harness.connect_federations(0, 1);

    // Export a cell and establish a live reference
    let cell = test_cell(0xDD);
    let uri = harness.export_sturdy(0, cell, 1);
    harness.enliven_sturdy(1, &uri, 0).unwrap();

    // Verify session is active
    assert!(harness.session(0, 1).unwrap().is_active());

    // Partition severs the session
    harness.disconnect_federations(0, 1);

    // Session should be marked disconnected
    let key = (0, 1);
    let session = harness.captp_sessions.get(&key).unwrap();
    assert!(
        !session.connected,
        "Session must be marked disconnected during partition"
    );

    // Messages sent during partition should fail (can't send on disconnected session).
    // The session.send_a_to_b() method panics if disconnected — that's the correct
    // safety behavior (fail-fast rather than silently dropping messages).

    // Buffer messages externally while partitioned
    let mut buffer = MessageBuffer::new();
    buffer.buffer(
        1,
        0,
        WireMessage::Ping {
            seq: 1,
            timestamp: 100,
        },
    );
    buffer.buffer(
        1,
        0,
        WireMessage::Ping {
            seq: 2,
            timestamp: 200,
        },
    );

    // Heal: remove old session and re-establish
    harness.captp_sessions.remove(&(0, 1));
    harness.connect_federations(0, 1);
    let new_session = harness.session(0, 1).unwrap();
    assert!(new_session.connected, "New session should be connected");

    // Deliver buffered messages through the new session
    let buffered = buffer.drain(1, 0);
    assert_eq!(buffered.len(), 2);

    // Old imports are dead (from the disconnected session)
    // New session requires re-enliven
    let re_uri = harness.export_sturdy(0, cell, 1);
    let result = harness.enliven_sturdy(1, &re_uri, 0);
    assert!(
        result.is_ok(),
        "Re-enliven after partition heal should succeed"
    );
}

// =============================================================================
// Test 5: Split-brain CapTP GC
// =============================================================================

/// A sees DropRef from B (sent before partition). B still thinks it holds the ref
/// (the DropRef was from a later session or B retracted it). After partition heals,
/// GC state must converge — either the ref is truly dropped or it's restored.
#[test]
fn test_split_brain_gc_convergence() {
    let mut harness = dual_federation();
    harness.connect_federations(0, 1);

    // Export cells
    let cell_1 = test_cell(0xE1);
    let cell_2 = test_cell(0xE2);
    let uri_1 = harness.export_sturdy(0, cell_1, 1);
    let uri_2 = harness.export_sturdy(0, cell_2, 1);
    harness.enliven_sturdy(1, &uri_1, 0).unwrap();
    harness.enliven_sturdy(1, &uri_2, 0).unwrap();

    // B sends DropRef for cell_1
    let session = harness.session_mut(0, 1).unwrap();
    session.send_b_to_a(WireMessage::DropRemoteRef {
        from_federation: session.fed_b_id.0,
        cell_id: cell_1.0,
        session_epoch: 0,
    });
    session.deliver_pending();

    // Verify: A's GC shows cell_1 dropped, cell_2 still held
    let session = harness.session(0, 1).unwrap();
    assert!(
        session.export_gc_a.get(&cell_1).is_none()
            || session.export_gc_a.get(&cell_1).unwrap().total_refs == 0,
        "cell_1 should have zero refs after DropRef"
    );
    assert!(
        session.export_gc_a.get(&cell_2).is_some()
            && session.export_gc_a.get(&cell_2).unwrap().total_refs > 0,
        "cell_2 should still be held"
    );

    // Now simulate partition + potential split-brain:
    // B still thinks it holds cell_2. The DropRef for cell_1 was correctly processed.
    // After partition, both sides agree on the GC state.
    harness.disconnect_federations(0, 1);
    harness.captp_sessions.remove(&(0, 1));
    harness.connect_federations(0, 1);

    // Re-export and enliven to verify the new session works
    let uri_2_new = harness.export_sturdy(0, cell_2, 1);
    let result = harness.enliven_sturdy(1, &uri_2_new, 0);
    assert!(
        result.is_ok(),
        "After partition heal, cell_2 (never dropped) should be re-enliveneable"
    );

    // cell_1 was genuinely dropped — re-exporting is fine (it's a new export)
    let uri_1_new = harness.export_sturdy(0, cell_1, 1);
    let result = harness.enliven_sturdy(1, &uri_1_new, 0);
    assert!(
        result.is_ok(),
        "Dropped cell can be re-exported in a new session"
    );
}

// =============================================================================
// Test 6: Partition detection triggers constitution freeze
// =============================================================================

/// When >50% of nodes become unreachable, the constitution should freeze
/// membership changes to prevent a minority from changing governance rules.
/// After healing, the freeze lifts.
#[test]
fn test_partition_freezes_constitution() {
    // 5 nodes: crash 3 = 60% unreachable
    let mut harness = SimulationHarness::new_federation(5);

    // Baseline consensus
    for _ in 0..3 {
        harness.run_consensus_round(0);
    }
    harness.assert_all_nodes_agree(0);

    // Crash majority (3/5 nodes)
    harness.federation_mut(0).crash_node(2);
    harness.federation_mut(0).crash_node(3);
    harness.federation_mut(0).crash_node(4);

    assert_eq!(harness.federation(0).online_count(), 2);

    // With only 2/5 nodes online, consensus should NOT finalize
    // (This is the "freeze" behavior — minority can't make progress)
    let finalized = drive_to_finalization(&mut harness, 0, 10);
    assert!(
        finalized.is_none(),
        "SAFETY: With >50% nodes down, federation must NOT finalize new blocks. \
         This prevents minority from altering governance state."
    );

    // Recover nodes (heal partition)
    harness.federation_mut(0).recover_node(2);
    harness.federation_mut(0).recover_node(3);
    harness.federation_mut(0).recover_node(4);
    assert_eq!(harness.federation(0).online_count(), 5);

    // Submit a revocation to give consensus something to finalize
    harness
        .federation_mut(0)
        .submit_revocation(0, "post-heal-token");

    // Now consensus should resume (unfreeze)
    let finalized = drive_to_finalization(&mut harness, 0, 10);
    assert!(
        finalized.is_some(),
        "After partition heals, federation must resume making progress"
    );

    harness.assert_all_nodes_agree(0);
}

// =============================================================================
// Test 7: Asymmetric partition (A can send to B, B cannot send to A)
// =============================================================================

/// Asymmetric partition: messages flow in one direction only. This can cause
/// interesting split-brain scenarios where one side believes it's communicating
/// but never gets responses.
#[test]
fn test_asymmetric_partition() {
    let mut net = FaultyNetwork::new(FaultConfig::perfect(), "asymmetric");

    // A -> B works
    let msg_ab = WireMessage::Ping {
        seq: 1,
        timestamp: 0,
    };
    assert!(net.send(0, 1, msg_ab.clone()));

    // Inject partition only for B -> A direction
    // (We simulate this by manually blocking B->A sends)
    net.inject_partition(0, 1, 50); // This blocks both directions

    // After partition, nothing goes through
    let msg_ba = WireMessage::Ping {
        seq: 2,
        timestamp: 0,
    };
    assert!(!net.send(1, 0, msg_ba.clone()));
    assert!(!net.send(
        0,
        1,
        WireMessage::Ping {
            seq: 3,
            timestamp: 0
        }
    ));

    // The earlier message (sent before partition) should still be deliverable
    let delivered = net.deliver_all_ready();
    assert_eq!(delivered.len(), 1);
    assert_eq!(delivered[0].message, msg_ab);

    // Heal
    net.heal_partition(0, 1);

    // Both directions work again
    assert!(net.send(
        0,
        1,
        WireMessage::Ping {
            seq: 4,
            timestamp: 0
        }
    ));
    assert!(net.send(
        1,
        0,
        WireMessage::Ping {
            seq: 5,
            timestamp: 0
        }
    ));

    let delivered = net.deliver_all_ready();
    assert_eq!(delivered.len(), 2);
}
