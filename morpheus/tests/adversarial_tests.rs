//! Adversarial / Byzantine fault-tolerance tests for the Morpheus BFT protocol.
//!
//! These tests verify that safety properties hold under Byzantine behavior:
//! equivocating leaders, double-voting, forged signatures, non-member messages,
//! view-jump attacks, out-of-order delivery, and leader failure with view change.
//!
//! Each test injects specific Byzantine behavior and asserts that the protocol
//! detects and rejects it (safety) or recovers from it (liveness).
//!
//! NOTE: The test harness uses `vec![SecretKey::random(&mut test_rng()); N]`
//! which creates identical keys for all nodes (clone semantics). Therefore,
//! tests that require distinguishable signatures must use a key that is truly
//! outside the committee setup (e.g., `SecretKey::dummy()`).

use ark_serialize::CanonicalSerialize;
use pyana_morpheus::test_harness::{SimulationHarness, TestTransaction, TxGenPolicy};
use pyana_morpheus::*;
use std::sync::Arc;

// =============================================================================
// Test 1: Equivocating leader — two different blocks for the same slot
// =============================================================================

/// Safety property: if a Byzantine leader produces two different blocks for the
/// same (type, author, slot), honest nodes must reject the equivocation via the
/// `seen_slots` mechanism. Only the first block observed should be recorded.
#[test]
fn test_equivocating_leader_rejected() {
    let mut harness = SimulationHarness::create_test_setup(3);

    let genesis_qc = harness
        .processes
        .get(&Identity(1))
        .unwrap()
        .genesis_qc
        .clone();

    // Create two conflicting transaction blocks from Identity(2) at the same slot
    let block_key_a = BlockKey {
        type_: BlockType::Tr,
        view: ViewNum(0),
        height: 1,
        author: Some(Identity(2)),
        slot: SlotNum(0),
        hash: Some(BlockHash(0xAAAA)),
    };

    let block_key_b = BlockKey {
        type_: BlockType::Tr,
        view: ViewNum(0),
        height: 1,
        author: Some(Identity(2)),
        slot: SlotNum(0),
        hash: Some(BlockHash(0xBBBB)), // Different hash = different block
    };

    let block_a = Block {
        key: block_key_a.clone(),
        prev: vec![genesis_qc.clone()],
        one: genesis_qc.clone(),
        data: BlockData::Tr {
            transactions: vec![TestTransaction(vec![1, 2, 3])],
        },
    };

    let block_b = Block {
        key: block_key_b.clone(),
        prev: vec![genesis_qc.clone()],
        one: genesis_qc.clone(),
        data: BlockData::Tr {
            transactions: vec![TestTransaction(vec![4, 5, 6])],
        },
    };

    // Sign both blocks with Identity(2)'s key
    let kb_2 = harness.processes.get(&Identity(2)).unwrap().kb.clone();
    let signed_a = Arc::new(Signed::from_data(block_a, &kb_2));
    let signed_b = Arc::new(Signed::from_data(block_b, &kb_2));

    // Deliver block A directly to nodes 1 and 3 (simulating Byzantine leader
    // sending to honest nodes; the harness skips sender on broadcast)
    harness.enqueue_message(
        Message::Block(signed_a.clone()),
        Identity(2),
        Some(Identity(1)),
    );
    harness.enqueue_message(
        Message::Block(signed_a.clone()),
        Identity(2),
        Some(Identity(3)),
    );
    harness.process_round();

    // Block A should be recorded by nodes 1 and 3
    for id in [1u32, 3] {
        let process = harness.processes.get(&Identity(id)).unwrap();
        assert!(
            process.index.blocks.contains_key(&block_key_a),
            "node {} should have recorded block A",
            id
        );
    }

    // Now deliver the equivocating block B to the same nodes
    harness.enqueue_message(
        Message::Block(signed_b.clone()),
        Identity(2),
        Some(Identity(1)),
    );
    harness.enqueue_message(
        Message::Block(signed_b.clone()),
        Identity(2),
        Some(Identity(3)),
    );
    harness.process_round();

    // Block B must NOT be recorded — the seen_slots mechanism rejects it
    for id in [1u32, 3] {
        let process = harness.processes.get(&Identity(id)).unwrap();
        assert!(
            !process.index.blocks.contains_key(&block_key_b),
            "node {} must reject equivocating block B (same type/author/slot as A)",
            id
        );
    }

    // Verify invariants still hold after processing the equivocation attempt
    for (id, process) in harness.processes.iter() {
        let violations = process.check_invariants();
        assert!(
            violations.is_empty(),
            "node {:?} has invariant violations after equivocation: {:?}",
            id,
            violations
        );
    }
}

// =============================================================================
// Test 2: Double-voting node — same author votes twice for same data
// =============================================================================

/// Safety property: QuorumTrack must reject a second vote from the same author
/// for the same VoteData. A Byzantine node sending duplicate votes must not be
/// able to inflate the vote count toward quorum.
#[test]
fn test_double_voting_rejected_by_quorum_track() {
    let mut harness = SimulationHarness::create_test_setup(3);

    let kb_1 = harness.processes.get(&Identity(1)).unwrap().kb.clone();

    // Create a vote for the genesis block
    let vote_data = VoteData {
        z: 0,
        for_which: BlockKey {
            type_: BlockType::Tr,
            view: ViewNum(0),
            height: 1,
            author: Some(Identity(2)),
            slot: SlotNum(0),
            hash: Some(BlockHash(0x1234)),
        },
    };

    // Create two votes with the same author (Identity(1)) for the same VoteData
    let vote_1 = Arc::new(ThreshPartial::from_data(vote_data.clone(), &kb_1));
    let vote_2 = Arc::new(ThreshPartial::from_data(vote_data.clone(), &kb_1));

    // Deliver the first vote to node 2
    let process_2 = harness.processes.get_mut(&Identity(2)).unwrap();
    let mut to_send = Vec::new();

    // First vote should be accepted
    let result_1 = process_2.record_vote(&vote_1, &mut to_send);
    assert!(result_1, "first vote from Identity(1) should be accepted");

    // Second vote from same author should be rejected (returns false = duplicate)
    let result_2 = process_2.record_vote(&vote_2, &mut to_send);
    assert!(
        !result_2,
        "second vote from same Identity(1) for same VoteData must be rejected"
    );

    // The vote count should still be 1, not 2
    let count = process_2
        .vote_tracker
        .votes
        .get(&vote_data)
        .map(|m| m.len())
        .unwrap_or(0);
    assert_eq!(
        count, 1,
        "vote count must be 1 after duplicate rejection, got {}",
        count
    );
}

// =============================================================================
// Test 3: Invalid signature — forged vote rejected before processing
// =============================================================================

/// Safety property: a message with a forged/invalid signature must be rejected
/// at the signature-verification stage, before any protocol state is mutated.
///
/// NOTE: Since the test harness uses identical keys for all nodes, we forge with
/// a completely external key (`SecretKey::dummy()`) that is NOT part of the committee.
#[test]
fn test_invalid_signature_vote_rejected() {
    let mut harness = SimulationHarness::create_test_setup(3);

    let kb_1 = harness.processes.get(&Identity(1)).unwrap().kb.clone();

    let vote_data = VoteData {
        z: 0,
        for_which: BlockKey {
            type_: BlockType::Tr,
            view: ViewNum(0),
            height: 1,
            author: Some(Identity(2)),
            slot: SlotNum(0),
            hash: Some(BlockHash(0x5678)),
        },
    };

    // Sign with a completely different key (dummy key, not in the committee)
    let dummy_sk = hints::SecretKey::dummy();
    let mut buf = Vec::new();
    vote_data.serialize_compressed(&mut buf).unwrap();
    let forged_sig = hints::sign(&dummy_sk, &buf);

    let forged_vote = ThreshPartial {
        data: vote_data.clone(),
        author: Identity(1), // Claims to be node 1
        signature: forged_sig,
    };

    let forged_msg = Message::NewVote(Arc::new(forged_vote));

    // Deliver the forged vote to node 3
    harness.enqueue_message(forged_msg, Identity(1), Some(Identity(3)));
    harness.process_round();

    // Node 3's vote tracker should NOT have recorded this vote
    let process_3 = harness.processes.get(&Identity(3)).unwrap();
    let has_vote = process_3
        .vote_tracker
        .votes
        .get(&vote_data)
        .map(|m| m.contains_key(&Identity(1)))
        .unwrap_or(false);
    assert!(
        !has_vote,
        "forged vote (wrong signature from dummy key) must not be recorded in vote tracker"
    );
}

/// Safety property: a block with an invalid signature must be rejected.
///
/// Uses a key external to the committee so the pairing check actually fails.
#[test]
fn test_invalid_signature_block_rejected() {
    let mut harness = SimulationHarness::create_test_setup(3);

    let genesis_qc = harness
        .processes
        .get(&Identity(1))
        .unwrap()
        .genesis_qc
        .clone();

    let block_key = BlockKey {
        type_: BlockType::Tr,
        view: ViewNum(0),
        height: 1,
        author: Some(Identity(2)),
        slot: SlotNum(0),
        hash: Some(BlockHash(0x9ABC)),
    };

    let block = Block {
        key: block_key.clone(),
        prev: vec![genesis_qc.clone()],
        one: genesis_qc.clone(),
        data: BlockData::Tr {
            transactions: vec![TestTransaction(vec![7, 8, 9])],
        },
    };

    // Sign with a dummy key that is NOT in the committee
    let dummy_sk = hints::SecretKey::dummy();
    let mut buf = Vec::new();
    Block::<TestTransaction>::serialize_compressed(&block, &mut buf).unwrap();
    let forged_sig = hints::sign(&dummy_sk, &buf);

    let forged_block = Signed {
        data: block,
        author: Identity(2),
        signature: forged_sig,
    };

    let forged_msg = Message::Block(Arc::new(forged_block));

    // Deliver to nodes 1 and 3
    harness.enqueue_message(forged_msg.clone(), Identity(2), Some(Identity(1)));
    harness.enqueue_message(forged_msg, Identity(2), Some(Identity(3)));
    harness.process_round();

    // No node should have recorded this block
    for id in [1u32, 3] {
        let process = harness.processes.get(&Identity(id)).unwrap();
        assert!(
            !process.index.blocks.contains_key(&block_key),
            "node {} must reject block with invalid signature (dummy key)",
            id
        );
    }
}

// =============================================================================
// Test 4: Message from non-member — unknown identity rejected
// =============================================================================

/// Safety property: a message from an Identity not in the committee must be
/// rejected. The `valid_signature` check should fail because the key is not
/// in the KeyBook.
#[test]
fn test_message_from_non_member_rejected() {
    let mut harness = SimulationHarness::create_test_setup(3);

    // Create a fake identity that is NOT in the committee (Identity(99))
    // We'll manually construct a ThreshPartial with this unknown author
    let kb_1 = harness.processes.get(&Identity(1)).unwrap().kb.clone();

    let vote_data = VoteData {
        z: 0,
        for_which: BlockKey {
            type_: BlockType::Tr,
            view: ViewNum(0),
            height: 1,
            author: Some(Identity(2)),
            slot: SlotNum(0),
            hash: Some(BlockHash(0xDEAD)),
        },
    };

    // Create a vote signed by node 1 but claim it's from non-member Identity(99)
    let mut non_member_vote = ThreshPartial::from_data(vote_data.clone(), &kb_1);
    non_member_vote.author = Identity(99); // Non-existent committee member

    let non_member_msg = Message::NewVote(Arc::new(non_member_vote));

    // Deliver to node 2
    harness.enqueue_message(non_member_msg, Identity(99), Some(Identity(2)));
    harness.process_round();

    // Node 2 should not have recorded this vote
    let process_2 = harness.processes.get(&Identity(2)).unwrap();
    let has_vote = process_2
        .vote_tracker
        .votes
        .get(&vote_data)
        .map(|m| m.contains_key(&Identity(99)))
        .unwrap_or(false);
    assert!(
        !has_vote,
        "vote from non-member Identity(99) must be rejected"
    );
}

/// Safety property: an EndView message from a non-member is rejected.
#[test]
fn test_end_view_from_non_member_rejected() {
    let mut harness = SimulationHarness::create_test_setup(3);

    let kb_1 = harness.processes.get(&Identity(1)).unwrap().kb.clone();

    // Create an EndView signed by node 1 but claim it's from non-member Identity(50)
    let mut non_member_end_view = ThreshPartial::from_data(ViewNum(0), &kb_1);
    non_member_end_view.author = Identity(50);

    let msg = Message::EndView(Arc::new(non_member_end_view));

    // Deliver to node 2
    harness.enqueue_message(msg, Identity(50), Some(Identity(2)));
    harness.process_round();

    // Node 2's end_views should NOT have any vote from Identity(50)
    let process_2 = harness.processes.get(&Identity(2)).unwrap();
    let has_end_view = process_2
        .end_views
        .votes
        .get(&ViewNum(0))
        .map(|m| m.contains_key(&Identity(50)))
        .unwrap_or(false);
    assert!(
        !has_end_view,
        "EndView from non-member Identity(50) must be rejected"
    );
}

// =============================================================================
// Test 5: View-jump attack — EndViewCert jumping more than max_view_jump
// =============================================================================

/// Safety property: an EndViewCert that would advance the view by more than
/// f+2 must be rejected to prevent a Byzantine node from forcing an arbitrarily
/// large view skip.
#[test]
fn test_view_jump_attack_rejected() {
    let mut harness = SimulationHarness::create_test_setup(3);

    // With n=3, f=0, so max_view_jump = f+2 = 2.
    // Current view is 0. A cert for view 0 would advance to view 1 (ok).
    // A cert for view 1 would advance to view 2 (ok, jump=2).
    // A cert for view 2 would advance to view 3 (jump=3, REJECTED).

    let kb_1 = harness.processes.get(&Identity(1)).unwrap().kb.clone();
    let kb_2 = harness.processes.get(&Identity(2)).unwrap().kb.clone();
    let kb_3 = harness.processes.get(&Identity(3)).unwrap().kb.clone();

    // Create a legitimate-looking EndViewCert for view 99 (huge jump)
    // We need to create a threshold signature. With f=0, threshold = f+1 = 1.
    let far_view = ViewNum(99);
    let vote_1 = ThreshPartial::from_data(far_view, &kb_1);

    let agg = kb_1.hints_setup.aggregator();
    let mut data_buf = Vec::new();
    far_view.serialize_compressed(&mut data_buf).unwrap();

    let signed = hints::sign_aggregate(
        &agg,
        hints::F::from(1u64), // threshold = f+1 = 1
        &[(0, vote_1.signature.clone())],
        &data_buf,
    )
    .unwrap();

    let evil_cert = Arc::new(ThreshSigned {
        data: far_view,
        signature: signed,
    });

    // Verify the cert would pass signature validation (it's legitimately signed)
    assert!(
        evil_cert.valid_signature(&kb_1, 1),
        "the cert is properly signed (this tests the view-jump logic, not sig validation)"
    );

    // Deliver the cert to node 2
    let msg = Message::EndViewCert(evil_cert);
    harness.enqueue_message(msg, Identity(1), Some(Identity(2)));
    harness.process_round();

    // Node 2 should still be in view 0 — the huge jump was rejected
    let process_2 = harness.processes.get(&Identity(2)).unwrap();
    assert_eq!(
        process_2.view_i,
        ViewNum(0),
        "node 2 must reject EndViewCert with view jump > max_view_jump (f+2=2), still in view 0"
    );
}

/// Verify that a legitimate EndViewCert within the max_view_jump bound IS accepted.
#[test]
fn test_legitimate_view_advance_accepted() {
    let mut harness = SimulationHarness::create_test_setup(3);

    // With n=3, f=0: max_view_jump = f+2 = 2.
    // Current view is 0. A cert for view 0 advances to view 1 (jump=1, ok).
    let kb_1 = harness.processes.get(&Identity(1)).unwrap().kb.clone();

    let cert_view = ViewNum(0); // certifying end of view 0 => advance to view 1
    let vote_1 = ThreshPartial::from_data(cert_view, &kb_1);

    let agg = kb_1.hints_setup.aggregator();
    let mut data_buf = Vec::new();
    cert_view.serialize_compressed(&mut data_buf).unwrap();

    let signed = hints::sign_aggregate(
        &agg,
        hints::F::from(1u64),
        &[(0, vote_1.signature.clone())],
        &data_buf,
    )
    .unwrap();

    let legit_cert = Arc::new(ThreshSigned {
        data: cert_view,
        signature: signed,
    });

    let msg = Message::EndViewCert(legit_cert);
    harness.enqueue_message(msg, Identity(1), Some(Identity(2)));
    harness.process_round();

    // Node 2 should advance to view 1
    let process_2 = harness.processes.get(&Identity(2)).unwrap();
    assert_eq!(
        process_2.view_i,
        ViewNum(1),
        "node 2 should accept EndViewCert advancing to view 1 (within max_view_jump)"
    );
}

// =============================================================================
// Test 6: Out-of-order delivery — messages for future views/heights
// =============================================================================

/// Liveness property: messages arriving for future views should not crash the node.
/// The protocol should either buffer them or safely reject them without panicking.
#[test]
fn test_out_of_order_future_view_messages_no_crash() {
    let mut harness = SimulationHarness::create_test_setup(3);

    let kb_2 = harness.processes.get(&Identity(2)).unwrap().kb.clone();

    // Create an EndView message for a future view (view 5) while all nodes are in view 0
    let future_end_view = Arc::new(ThreshPartial::from_data(ViewNum(5), &kb_2));
    let future_msg = Message::EndView(future_end_view);

    // Deliver to node 1 (which is in view 0)
    harness.enqueue_message(future_msg.clone(), Identity(2), Some(Identity(1)));

    // This should not panic
    harness.process_round();

    // Node 1 should still be functional (in view 0 or possibly advanced, but not crashed)
    let process_1 = harness.processes.get(&Identity(1)).unwrap();
    // The node should still have valid state
    let violations = process_1.check_invariants();
    assert!(
        violations.is_empty(),
        "node 1 should have no invariant violations after receiving future-view message: {:?}",
        violations
    );
}

/// Liveness property: a vote for a block that hasn't been received yet should
/// not crash the node.
#[test]
fn test_vote_for_unknown_block_no_crash() {
    let mut harness = SimulationHarness::create_test_setup(3);

    let kb_1 = harness.processes.get(&Identity(1)).unwrap().kb.clone();

    // Create a vote for a block that no node has ever seen
    let unknown_block_key = BlockKey {
        type_: BlockType::Tr,
        view: ViewNum(0),
        height: 42,
        author: Some(Identity(3)),
        slot: SlotNum(100),
        hash: Some(BlockHash(0xFEEDFACE)),
    };

    let vote = Arc::new(ThreshPartial::from_data(
        VoteData {
            z: 0,
            for_which: unknown_block_key,
        },
        &kb_1,
    ));

    let msg = Message::NewVote(vote);

    // Deliver to node 2 — should not crash
    harness.enqueue_message(msg, Identity(1), Some(Identity(2)));
    harness.process_round();

    // Node 2 should still be in a valid state
    let process_2 = harness.processes.get(&Identity(2)).unwrap();
    let violations = process_2.check_invariants();
    assert!(
        violations.is_empty(),
        "node 2 should have no invariant violations after vote for unknown block: {:?}",
        violations
    );
}

/// Liveness property: a QC for a future view should not crash the node.
/// The protocol may advance the view or ignore it, but must remain consistent.
#[test]
fn test_qc_for_future_view_no_crash() {
    let mut harness = SimulationHarness::create_test_setup(3);

    let kb_1 = harness.processes.get(&Identity(1)).unwrap().kb.clone();
    let kb_2 = harness.processes.get(&Identity(2)).unwrap().kb.clone();
    let kb_3 = harness.processes.get(&Identity(3)).unwrap().kb.clone();

    // Create a valid QC for a block in a future view
    let future_block_key = BlockKey {
        type_: BlockType::Tr,
        view: ViewNum(3),
        height: 5,
        author: Some(Identity(2)),
        slot: SlotNum(2),
        hash: Some(BlockHash(0xCAFE)),
    };

    let vote_data = VoteData {
        z: 0,
        for_which: future_block_key,
    };

    // Create votes from all 3 nodes and aggregate
    let v1 = ThreshPartial::from_data(vote_data.clone(), &kb_1);
    let v2 = ThreshPartial::from_data(vote_data.clone(), &kb_2);
    let v3 = ThreshPartial::from_data(vote_data.clone(), &kb_3);

    let agg = kb_1.hints_setup.aggregator();
    let mut data_buf = Vec::new();
    vote_data.serialize_compressed(&mut data_buf).unwrap();

    let signed = hints::sign_aggregate(
        &agg,
        hints::F::from(3u64), // n - f = 3
        &[
            (0, v1.signature.clone()),
            (1, v2.signature.clone()),
            (2, v3.signature.clone()),
        ],
        &data_buf,
    )
    .unwrap();

    let future_qc = Arc::new(ThreshSigned {
        data: vote_data,
        signature: signed,
    });

    let msg = Message::QC(future_qc);
    harness.enqueue_message(msg, Identity(1), Some(Identity(2)));

    // Should not panic
    harness.process_round();

    // Node 2 should still be functional
    let process_2 = harness.processes.get(&Identity(2)).unwrap();
    let violations = process_2.check_invariants();
    assert!(
        violations.is_empty(),
        "node 2 should have no invariant violations after future-view QC: {:?}",
        violations
    );
}

// =============================================================================
// Test 7: Leader failure + view change — liveness under Byzantine leader
// =============================================================================

/// Liveness property: if the leader of view 0 is Byzantine (never produces blocks),
/// honest nodes must timeout, exchange EndView messages, form an EndViewCert,
/// advance to view 1, and the new leader must successfully produce and make progress.
///
/// The Byzantine leader (node 1) still participates in message processing (voting,
/// timeouts) — it just never produces blocks. This is the most realistic Byzantine
/// failure: a leader that "crashes" for block production but remains online.
#[test]
fn test_leader_failure_full_view_change_recovery() {
    let mut harness = SimulationHarness::create_test_setup(3);

    // Use larger time steps so we cross the 12*delta timeout faster (fewer BLS ops).
    harness.time_step = 500;

    // Leader of view 0 is Identity(1) (since leader = view % n + 1 = 0%3+1 = 1).
    // Node 1 is Byzantine: present but never produces any blocks (no transactions).
    harness
        .tx_gen_policy
        .insert(Identity(1), TxGenPolicy::Never);

    // Nodes 2 and 3 produce transactions
    harness
        .tx_gen_policy
        .insert(Identity(2), TxGenPolicy::EveryNSteps { n: 1 });
    harness
        .tx_gen_policy
        .insert(Identity(3), TxGenPolicy::EveryNSteps { n: 1 });

    // 12*delta = 1200, time_step = 500, so 3 steps crosses timeout.
    // Run 6 steps for timeout + message exchange + view advancement.
    harness.run(6);

    // All nodes should have advanced past view 0 via EndViewCert
    let max_view = harness.processes.values().map(|p| p.view_i).max().unwrap();
    assert!(
        max_view > ViewNum(0),
        "honest nodes must advance past view 0 after Byzantine leader failure, max_view={:?}",
        max_view
    );

    // Blocks should have been produced (transaction blocks from nodes 2, 3)
    let p2_blocks = harness
        .processes
        .get(&Identity(2))
        .unwrap()
        .index
        .blocks
        .len();
    assert!(
        p2_blocks > 1,
        "honest nodes should produce blocks even with Byzantine leader, got {}",
        p2_blocks
    );

    // All nodes should agree on block set
    let p1_blocks = harness
        .processes
        .get(&Identity(1))
        .unwrap()
        .index
        .blocks
        .len();
    let p3_blocks = harness
        .processes
        .get(&Identity(3))
        .unwrap()
        .index
        .blocks
        .len();
    assert_eq!(
        p1_blocks, p2_blocks,
        "nodes 1 and 2 should agree on block count ({} vs {})",
        p1_blocks, p2_blocks
    );
    assert_eq!(
        p2_blocks, p3_blocks,
        "nodes 2 and 3 should agree on block count ({} vs {})",
        p2_blocks, p3_blocks
    );

    // Verify no invariant violations
    for (id, process) in harness.processes.iter() {
        let violations = process.check_invariants();
        assert!(
            violations.is_empty(),
            "node {:?} has invariant violations after view change recovery: {:?}",
            id,
            violations
        );
    }
}

/// Liveness property: after the Byzantine leader is replaced, the new leader in
/// the next view should be able to produce leader blocks and drive finalization
/// forward (given enough time).
#[test]
#[ignore] // Longer-running test (~130s in debug due to BLS)
fn test_view_change_new_leader_produces_and_finalizes() {
    let mut harness = SimulationHarness::create_test_setup(3);

    // Make node 1 (leader of view 0) Byzantine: it participates in voting
    // but never produces blocks (no transactions, so no Tr blocks, and it
    // won't get enough tips for leader blocks either).
    harness
        .tx_gen_policy
        .insert(Identity(1), TxGenPolicy::Never);
    harness
        .tx_gen_policy
        .insert(Identity(2), TxGenPolicy::EveryNSteps { n: 2 });
    harness
        .tx_gen_policy
        .insert(Identity(3), TxGenPolicy::EveryNSteps { n: 2 });

    // Run for 30 steps: crosses 12*delta timeout, triggers view change,
    // new leader (Identity(2) for view 1) produces leader blocks
    harness.run(30);

    // Verify view advanced
    let max_view = harness.processes.values().map(|p| p.view_i).max().unwrap();
    assert!(
        max_view > ViewNum(0),
        "should advance past view 0, max_view={:?}",
        max_view
    );

    // Verify leader blocks exist (produced by the new leader in view 1+)
    let has_leader_blocks = harness
        .processes
        .get(&Identity(2))
        .unwrap()
        .index
        .blocks
        .keys()
        .any(|k| k.type_ == BlockType::Lead);
    assert!(
        has_leader_blocks,
        "new leader should produce leader blocks after view change"
    );

    // Safety: all nodes agree on finalized set
    let p1_finalized = &harness.processes.get(&Identity(1)).unwrap().index.finalized;
    let p2_finalized = &harness.processes.get(&Identity(2)).unwrap().index.finalized;
    let p3_finalized = &harness.processes.get(&Identity(3)).unwrap().index.finalized;

    assert_eq!(
        p1_finalized, p2_finalized,
        "SAFETY VIOLATION: nodes 1 and 2 disagree on finalized set"
    );
    assert_eq!(
        p2_finalized, p3_finalized,
        "SAFETY VIOLATION: nodes 2 and 3 disagree on finalized set"
    );
}

// =============================================================================
// Test 8: Double-voting via direct QuorumTrack manipulation
// =============================================================================

/// Safety property: the QuorumTrack data structure itself correctly rejects
/// duplicate votes at the structural level, regardless of message routing.
#[test]
fn test_quorum_track_rejects_duplicate_directly() {
    let harness = SimulationHarness::create_test_setup(3);
    let kb_1 = harness.processes.get(&Identity(1)).unwrap().kb.clone();
    let kb_2 = harness.processes.get(&Identity(2)).unwrap().kb.clone();

    let vote_data = VoteData {
        z: 0,
        for_which: BlockKey {
            type_: BlockType::Tr,
            view: ViewNum(0),
            height: 1,
            author: Some(Identity(3)),
            slot: SlotNum(0),
            hash: Some(BlockHash(0xBEEF)),
        },
    };

    let mut tracker: QuorumTrack<VoteData> = QuorumTrack {
        votes: std::collections::BTreeMap::new(),
    };

    // First vote from Identity(1) — accepted
    let vote_a = Arc::new(ThreshPartial::from_data(vote_data.clone(), &kb_1));
    let result = tracker.record_vote(vote_a.clone());
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), 1);

    // Second vote from Identity(1) — duplicate, rejected
    let vote_a_dup = Arc::new(ThreshPartial::from_data(vote_data.clone(), &kb_1));
    let result = tracker.record_vote(vote_a_dup);
    assert!(result.is_err(), "duplicate vote must return Err(Duplicate)");

    // Vote from Identity(2) — different author, accepted
    let vote_b = Arc::new(ThreshPartial::from_data(vote_data.clone(), &kb_2));
    let result = tracker.record_vote(vote_b);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), 2);
}

// =============================================================================
// Test 9: Forged EndView message — invalid signature on view change vote
// =============================================================================

/// Safety property: a forged EndView message (wrong signature) must be rejected.
/// This prevents a Byzantine node from triggering view changes it didn't author.
///
/// Uses a dummy key external to the committee for a truly invalid signature.
#[test]
fn test_forged_end_view_rejected() {
    let mut harness = SimulationHarness::create_test_setup(3);

    // Forge an EndView "from Identity(1)" using a dummy key not in the committee
    let dummy_sk = hints::SecretKey::dummy();
    let view = ViewNum(0);
    let mut buf = Vec::new();
    view.serialize_compressed(&mut buf).unwrap();
    let forged_sig = hints::sign(&dummy_sk, &buf);

    let forged_end_view = ThreshPartial {
        data: view,
        author: Identity(1),
        signature: forged_sig,
    };

    let msg = Message::EndView(Arc::new(forged_end_view));

    // Deliver to node 3
    harness.enqueue_message(msg, Identity(1), Some(Identity(3)));
    harness.process_round();

    // Node 3's end_views tracker should NOT have a vote attributed to Identity(1)
    let process_3 = harness.processes.get(&Identity(3)).unwrap();
    let has_forged = process_3
        .end_views
        .votes
        .get(&ViewNum(0))
        .map(|m| m.contains_key(&Identity(1)))
        .unwrap_or(false);
    assert!(
        !has_forged,
        "forged EndView with dummy key signature must be rejected"
    );
}
