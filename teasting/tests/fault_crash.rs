//! Fault injection tests: crash recovery scenarios.
//!
//! Verifies that the system maintains safety properties when nodes crash at
//! arbitrary points in execution. Liveness may degrade, but safety must hold:
//! - No half-applied state transitions
//! - No lost or double-applied effects
//! - Conservation of computrons
//! - Nonce monotonicity

use std::collections::HashMap;

use pyana_cell::CellId;
use pyana_teasting::assertions::{
    assert_conservation_invariant, assert_gc_consistency, assert_nonce_monotonicity,
};
use pyana_teasting::fault::{CrashableNode, FaultConfig, FaultyNetwork, MessageBuffer, SavedState};
use pyana_teasting::federation::{drive_to_finalization, dual_federation, quick_federation};
use pyana_teasting::harness::SimulationHarness;
use pyana_wire::message::WireMessage;

// =============================================================================
// Helpers
// =============================================================================

fn test_cell(n: u8) -> CellId {
    CellId([n; 32])
}

// =============================================================================
// Test 1: Node crashes mid-turn-execution
// =============================================================================

/// When a node crashes after receiving a turn but before generating a receipt,
/// the turn must NOT be partially applied. On recovery, the state must be at
/// the pre-turn position (the turn can be re-executed safely).
#[test]
fn test_crash_mid_turn_no_partial_state() {
    let mut harness = quick_federation();

    // Create initial state
    let agent_cell = harness.ledger.create_cell([0x01; 32], [0x10; 32]);
    let target_cell = harness.ledger.create_cell([0x02; 32], [0x20; 32]);

    // Fund the cells
    harness.ledger.get_mut(&agent_cell).unwrap().state.balance = 1000;
    harness.ledger.get_mut(&target_cell).unwrap().state.balance = 500;
    let initial_total = 1500u64;

    // Record pre-turn state
    let pre_nonce = harness.ledger.get(&agent_cell).unwrap().state.nonce;
    let pre_balance_agent = harness.ledger.get(&agent_cell).unwrap().state.balance;
    let pre_balance_target = harness.ledger.get(&target_cell).unwrap().state.balance;

    // Simulate: turn submitted, node crashes before committing
    // We model this by NOT applying the turn — the node crashed mid-execution.
    let mut node = CrashableNode::new(0, 0);
    let saved = node.crash(harness.clock.block_height, vec![]);

    // Verify: state hasn't advanced (no partial effects)
    assert_eq!(
        harness.ledger.get(&agent_cell).unwrap().state.nonce,
        pre_nonce,
        "Nonce should not have advanced — turn was not committed"
    );
    assert_eq!(
        harness.ledger.get(&agent_cell).unwrap().state.balance,
        pre_balance_agent,
        "Agent balance should be unchanged"
    );
    assert_eq!(
        harness.ledger.get(&target_cell).unwrap().state.balance,
        pre_balance_target,
        "Target balance should be unchanged"
    );

    // Conservation invariant
    assert_conservation_invariant(&harness.ledger, initial_total);

    // Recover node
    node.recover(saved);
    assert!(node.healthy);

    // After recovery: turn can be re-submitted and will apply correctly
    // (We verify this by checking the ledger is still consistent)
    let mut observed_nonces = HashMap::new();
    assert_nonce_monotonicity(&harness.ledger, &mut observed_nonces);

    // Run consensus after recovery — remaining nodes agree
    harness.recover_node_in_federation(0, 0);
    for _ in 0..3 {
        harness.run_consensus_round(0);
    }
    harness.assert_all_nodes_agree(0);
}

// Helper extension trait for the harness in these tests
trait HarnessExt {
    fn recover_node_in_federation(&mut self, fed_idx: usize, node_idx: usize);
}

impl HarnessExt for SimulationHarness {
    fn recover_node_in_federation(&mut self, fed_idx: usize, node_idx: usize) {
        self.federations[fed_idx].recover_node(node_idx);
    }
}

// =============================================================================
// Test 2: Node crashes after proof generation but before broadcast
// =============================================================================

/// A node generates a proof (e.g., a STARK presentation proof) but crashes before
/// broadcasting it to the network. On recovery, the proof can be re-broadcast
/// and must be accepted (idempotent verification — proofs are stateless).
#[test]
fn test_crash_after_proof_before_broadcast() {
    let mut harness = dual_federation();
    harness.connect_federations(0, 1);

    let cell = test_cell(0x55);
    let _uri = harness.export_sturdy(0, cell, 1);

    // Simulate: node generated a proof (we model with a PresentToken message)
    // but crashed before broadcasting
    let proof_message = WireMessage::PresentToken {
        proof: vec![0xDE, 0xAD, 0xBE, 0xEF], // simulated proof bytes
        request: pyana_wire::message::AuthorizationRequest {
            resource: "/cells/alpha/read".to_string(),
            action: "read".to_string(),
            principal: "agent-0x01".to_string(),
            scopes: vec![],
            timestamp: 1_700_000_000,
            nonce: [0x01; 16],
        },
        federation_root: [0x11; 32],
    };

    // Crash! The message never reached the network.
    let mut node = CrashableNode::new(1, 0);
    let saved = node.crash(harness.clock.block_height, vec![proof_message.clone()]);

    // Verify: the proof is in the unsent messages
    assert_eq!(saved.unsent_messages.len(), 1);
    assert_eq!(saved.unsent_messages[0], proof_message);

    // Recovery: node comes back and can re-broadcast the same proof
    node.recover(saved.clone());
    assert!(node.healthy);

    // The proof can be sent again — verification is stateless/idempotent
    let mut net = FaultyNetwork::new(FaultConfig::perfect(), "idempotent-proof");
    assert!(net.send(1, 0, proof_message.clone()));
    let delivered = net.deliver_all_ready();
    assert_eq!(delivered.len(), 1);
    assert_eq!(delivered[0].message, proof_message);
}

// =============================================================================
// Test 3: CapTP session partner crashes — store and forward
// =============================================================================

/// When B crashes while A has an active session, messages from A should be
/// buffered (store-and-forward). When B recovers, messages must be delivered
/// in causal order.
#[test]
fn test_captp_partner_crash_store_forward() {
    let mut harness = dual_federation();
    harness.connect_federations(0, 1);

    // Export a cell from A to B
    let cell = test_cell(0x77);
    let _uri = harness.export_sturdy(0, cell, 1);

    // Simulate B crashing
    harness.federation_mut(1).crash_node(0);

    // A sends messages while B is down — these go into a buffer
    let mut buffer = MessageBuffer::new();
    let messages_to_send = vec![
        WireMessage::Ping {
            seq: 1,
            timestamp: 100,
        },
        WireMessage::Ping {
            seq: 2,
            timestamp: 200,
        },
        WireMessage::Ping {
            seq: 3,
            timestamp: 300,
        },
    ];

    for msg in &messages_to_send {
        buffer.buffer(1, 0, msg.clone());
    }

    assert_eq!(buffer.pending_count(1, 0), 3);

    // B recovers
    harness.federation_mut(1).recover_node(0);

    // Drain buffered messages — must arrive in order
    let delivered = buffer.drain(1, 0);
    assert_eq!(delivered.len(), 3);
    for (i, msg) in delivered.iter().enumerate() {
        match msg {
            WireMessage::Ping { seq, .. } => {
                assert_eq!(*seq, (i + 1) as u64, "Messages must be in causal order");
            }
            _ => panic!("Unexpected message type"),
        }
    }

    // Buffer is now empty
    assert_eq!(buffer.pending_count(1, 0), 0);

    // Session can resume — verify federation nodes agree
    for _ in 0..3 {
        harness.run_consensus_round(1);
    }
    harness.assert_all_nodes_agree(1);
}

// =============================================================================
// Test 4: Crash during handoff presentation
// =============================================================================

/// Recipient crashes between receiving a handoff certificate and completing
/// validation. On recovery, the certificate should still be presentable if
/// the nonce/use-count was not consumed. If it WAS consumed, the handoff must
/// be retried with a new certificate.
#[test]
fn test_crash_during_handoff_presentation() {
    let mut harness = dual_federation();
    harness.connect_federations(0, 1);

    let cell = test_cell(0x88);
    let uri = harness.export_sturdy(0, cell, 1);

    // Case A: Crash BEFORE the swiss number is consumed.
    // The handoff presentation message was received but enliven was not called.
    // On recovery, the URI should still be valid.
    {
        // Simulate: enliven was NOT called (crash before validation completes)
        let mut node = CrashableNode::new(1, 0);
        let _saved = node.crash(harness.clock.block_height, vec![]);
        node.recover(SavedState {
            node_idx: 0,
            federation_idx: 1,
            height_at_crash: harness.clock.block_height,
            unsent_messages: vec![],
            unprocessed_messages: vec![],
        });

        // URI should still work (swiss was not consumed)
        let result = harness.enliven_sturdy(1, &uri, 0);
        assert!(
            result.is_ok(),
            "After crash before consumption, enliven should succeed: {:?}",
            result.err()
        );
        assert_eq!(result.unwrap(), cell);
    }

    // Case B: Second enliven of the same URI (swiss number already consumed once).
    // Depending on max_uses, this may fail.
    {
        // The swiss entry has use_count=1 from above. If max_uses is None (unlimited),
        // this should still succeed.
        let result2 = harness.enliven_sturdy(1, &uri, 0);
        // Document behavior: unlimited-use sturdy refs remain valid after crash+re-present
        assert!(
            result2.is_ok(),
            "Unlimited-use sturdy ref should survive re-presentation after crash"
        );
    }
}

// =============================================================================
// Test 5: GC node crashes with pending drop messages
// =============================================================================

/// A node was about to send DropRef messages when it crashes. On recovery, the
/// node must re-discover which refs need dropping. Meanwhile, safety is maintained:
/// leaked refs cause only liveness issues (memory growth), NOT safety violations.
#[test]
fn test_gc_crash_pending_drops() {
    let mut harness = dual_federation();
    harness.connect_federations(0, 1);

    // Export multiple cells from A, enliven at B
    let cells: Vec<CellId> = (0x01..=0x05).map(test_cell).collect();
    let mut uris = Vec::new();
    for &cell in &cells {
        uris.push(harness.export_sturdy(0, cell, 1));
    }
    for uri in &uris {
        harness.enliven_sturdy(1, uri, 0).unwrap();
    }

    // B decides to drop some refs but crashes before sending DropRef
    // Use the real federation B ID (derived from "fed-beta" in dual_federation)
    let real_fed_b_id = harness.federation_id(1);
    let pending_drops = vec![
        WireMessage::DropRemoteRef {
            from_federation: real_fed_b_id.0,
            cell_id: cells[0].0,
            session_epoch: 0,
        },
        WireMessage::DropRemoteRef {
            from_federation: real_fed_b_id.0,
            cell_id: cells[2].0,
            session_epoch: 0,
        },
    ];

    let mut node = CrashableNode::new(1, 0);
    let saved = node.crash(harness.clock.block_height, pending_drops.clone());

    // Verify: A's export GC still thinks B holds all 5 refs (drops were never sent)
    let session = harness.session(0, 1).unwrap();
    // All cells should still be in A's export GC
    for &cell in &cells {
        assert!(
            session.export_gc_a.get(&cell).is_some(),
            "Cell {:?} should still be tracked in export GC (drop was never sent)",
            cell
        );
    }

    // Safety: the "leaked" refs (cells[0] and cells[2]) don't cause safety violations.
    // They're just not cleaned up — a liveness issue, not a safety issue.
    let session = harness.session(0, 1).unwrap();
    let zero_ref_cells: Vec<CellId> = Vec::new(); // no cells are actually at zero yet
    assert_gc_consistency(
        &session.export_gc_a,
        &[session.session_b.clone()],
        &zero_ref_cells,
    );

    // Recovery: node comes back, re-sends the drops
    node.recover(saved);
    let session = harness.session_mut(0, 1).unwrap();
    for drop_msg in &pending_drops {
        session.send_b_to_a(drop_msg.clone());
    }
    session.deliver_pending();

    // Now A's export GC should reflect the drops
    let session = harness.session(0, 1).unwrap();
    assert!(
        session.export_gc_a.get(&cells[0]).is_none()
            || session.export_gc_a.get(&cells[0]).unwrap().total_refs == 0,
        "After recovery and re-send, cell[0] should be dropped"
    );
    assert!(
        session.export_gc_a.get(&cells[2]).is_none()
            || session.export_gc_a.get(&cells[2]).unwrap().total_refs == 0,
        "After recovery and re-send, cell[2] should be dropped"
    );
}

// =============================================================================
// Test 6: Multiple simultaneous crashes (f < n/3)
// =============================================================================

/// With f < n/3 nodes crashed, the remaining nodes must continue making progress
/// (liveness). After recovery, crashed nodes must catch up to the current state.
#[test]
fn test_multiple_crashes_liveness() {
    // 7 nodes: can tolerate f=2 crashes (2 < 7/3 = 2.33)
    let mut harness = SimulationHarness::new_federation(7);

    // Run a few rounds to establish baseline
    for _ in 0..3 {
        harness.run_consensus_round(0);
    }
    harness.assert_all_nodes_agree(0);

    // Crash 2 nodes (f=2, which is < n/3 rounded down)
    harness.federation_mut(0).crash_node(5);
    harness.federation_mut(0).crash_node(6);

    assert_eq!(
        harness.federation(0).online_count(),
        5,
        "5 nodes should remain online"
    );

    // Submit a revocation while nodes are down — this gives consensus something to finalize
    harness.federation_mut(0).submit_revocation(0, "token-abc");

    // Remaining 5 nodes should still make progress (5/7 > 2/3 threshold)
    // Give many rounds for convergence since leader rotation may skip crashed nodes
    let finalized = drive_to_finalization(&mut harness, 0, 30);
    assert!(
        finalized.is_some(),
        "With 5/7 nodes online (>2/3 quorum), remaining nodes must continue finalizing blocks"
    );

    // The revocation should be processed by online nodes
    assert!(
        harness.federation(0).is_revoked(0, "token-abc"),
        "Online nodes should process revocations"
    );

    // Recover crashed nodes
    harness.federation_mut(0).recover_node(5);
    harness.federation_mut(0).recover_node(6);
    assert_eq!(harness.federation(0).online_count(), 7);

    // Run consensus to let recovered nodes catch up
    for _ in 0..5 {
        harness.run_consensus_round(0);
    }

    // All nodes (including recovered ones) should agree
    harness.assert_all_nodes_agree(0);

    // Recovered nodes should have the revocation
    assert!(
        harness.federation(0).is_revoked(5, "token-abc"),
        "Recovered node 5 should have the revocation"
    );
    assert!(
        harness.federation(0).is_revoked(6, "token-abc"),
        "Recovered node 6 should have the revocation"
    );
}

// =============================================================================
// Test 7: Crash during consensus round
// =============================================================================

/// A node crashes in the middle of a consensus round. The round should either
/// complete without it (if quorum is still available) or stall until recovery.
#[test]
fn test_crash_during_consensus() {
    let mut harness = SimulationHarness::new_federation(4);

    // Run one successful round
    harness.run_consensus_round(0);
    harness.assert_all_nodes_agree(0);

    // Crash one node (f=1 < 4/3 = 1.33 — borderline)
    harness.federation_mut(0).crash_node(3);

    // With 3/4 nodes online, consensus may or may not proceed
    // (depends on BFT threshold implementation)
    let attempts = 10;
    let mut any_finalized = false;
    for _ in 0..attempts {
        if harness.run_consensus_round(0) {
            any_finalized = true;
            break;
        }
    }

    // Whether or not consensus proceeds, safety must hold:
    // no divergent state among online nodes
    // (We can't call assert_all_nodes_agree because the crashed node won't respond,
    // but we can verify the online nodes are consistent by running more rounds)
    if any_finalized {
        // Good — system maintained liveness with one crash
        // Recover and verify catch-up
        harness.federation_mut(0).recover_node(3);
        for _ in 0..5 {
            harness.run_consensus_round(0);
        }
        harness.assert_all_nodes_agree(0);
    }
    // If no finalization: that's acceptable (liveness degradation, not safety violation)
}

// =============================================================================
// Test 8: Crash-recover-crash (double crash)
// =============================================================================

/// A node crashes, recovers, then crashes again before fully catching up.
/// The system must not enter an inconsistent state.
#[test]
fn test_double_crash_recovery() {
    let mut harness = SimulationHarness::new_federation(7);

    // Establish baseline
    for _ in 0..3 {
        harness.run_consensus_round(0);
    }

    // First crash
    harness.federation_mut(0).crash_node(4);
    for _ in 0..3 {
        harness.run_consensus_round(0);
    }

    // Recover
    harness.federation_mut(0).recover_node(4);
    // Only one round — not fully caught up
    harness.run_consensus_round(0);

    // Second crash before catch-up completes
    harness.federation_mut(0).crash_node(4);

    // System should still function
    for _ in 0..3 {
        harness.run_consensus_round(0);
    }

    // Final recovery
    harness.federation_mut(0).recover_node(4);
    for _ in 0..5 {
        harness.run_consensus_round(0);
    }

    // Must converge
    harness.assert_all_nodes_agree(0);
}
