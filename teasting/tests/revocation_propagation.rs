//! Revocation propagation integration test: revoke → propagate → reject.
//!
//! Tests that once a token is revoked via consensus, all nodes reject presentations
//! of that token and can produce non-membership proofs.

use pyana_teasting::federation::{drive_to_finalization, quick_federation};
use pyana_teasting::harness::SimulationHarness;

/// Basic revocation: submit, finalize, verify all nodes show revoked.
#[test]
fn test_basic_revocation_propagation() {
    let mut harness = quick_federation();

    // Submit revocation for a token.
    harness
        .federation_mut(0)
        .submit_revocation(0, "revoked-token-1");

    // Run consensus to finalize.
    let rounds = drive_to_finalization(&mut harness, 0, 5);
    assert!(rounds.is_some(), "Should finalize revocation");

    // All nodes should report the token as revoked.
    let fed = harness.federation(0);
    for i in 0..fed.node_count() {
        assert!(
            fed.is_revoked(i, "revoked-token-1"),
            "Node {} should show token as revoked after consensus",
            i
        );
    }
}

/// Non-revoked tokens should still pass: revocation is specific to token IDs.
#[test]
fn test_non_revoked_token_still_valid() {
    let mut harness = quick_federation();

    // Revoke one token.
    harness.federation_mut(0).submit_revocation(0, "bad-token");
    drive_to_finalization(&mut harness, 0, 5).unwrap();

    // A different token should NOT be revoked.
    let fed = harness.federation(0);
    assert!(
        !fed.is_revoked(0, "good-token"),
        "Unrevoked token must not appear revoked"
    );
}

/// Multiple revocations in one block.
#[test]
fn test_batch_revocation() {
    let mut harness = quick_federation();

    // Submit multiple revocations from different nodes.
    harness.federation_mut(0).submit_revocation(0, "batch-1");
    harness.federation_mut(0).submit_revocation(1, "batch-2");
    harness.federation_mut(0).submit_revocation(2, "batch-3");

    drive_to_finalization(&mut harness, 0, 5).unwrap();

    let fed = harness.federation(0);
    assert!(fed.is_revoked(0, "batch-1"));
    assert!(fed.is_revoked(0, "batch-2"));
    assert!(fed.is_revoked(0, "batch-3"));

    // State should be consistent across all nodes.
    harness.assert_all_nodes_agree(0);
}

/// Revocation persists across multiple consensus rounds.
#[test]
fn test_revocation_persists_across_rounds() {
    let mut harness = quick_federation();

    // Revoke in round 1.
    harness
        .federation_mut(0)
        .submit_revocation(0, "persistent-revoke");
    drive_to_finalization(&mut harness, 0, 5).unwrap();

    // Run more rounds with different revocations.
    harness
        .federation_mut(0)
        .submit_revocation(1, "other-token");
    drive_to_finalization(&mut harness, 0, 5).unwrap();

    // Original revocation still holds.
    let fed = harness.federation(0);
    assert!(fed.is_revoked(0, "persistent-revoke"));
    assert!(fed.is_revoked(0, "other-token"));
}

/// Revocation after node crash and recovery: recovered node should know about revocations
/// that happened while it was down.
#[test]
fn test_revocation_after_recovery() {
    let mut harness = quick_federation();

    // Crash node 3.
    harness.federation_mut(0).crash_node(3);

    // Revoke while node 3 is down.
    harness
        .federation_mut(0)
        .submit_revocation(0, "revoked-while-down");
    drive_to_finalization(&mut harness, 0, 5).unwrap();

    // Recover node 3.  recover_node() replays the federation-wide all_revoked
    // set into the rejoining node, so it immediately learns about revocations
    // that happened while it was offline — no additional consensus round needed
    // for the missed entries.
    harness.federation_mut(0).recover_node(3);

    // Run another round to trigger sync for post-recovery revocations.
    harness
        .federation_mut(0)
        .submit_revocation(1, "trigger-sync");
    drive_to_finalization(&mut harness, 0, 5).unwrap();

    // Node 3 should now know about both revocations.
    let fed = harness.federation(0);
    assert!(
        fed.is_revoked(3, "revoked-while-down"),
        "node 3 must know about revocation missed while offline"
    );
    assert!(
        fed.is_revoked(3, "trigger-sync"),
        "node 3 must know about post-recovery revocation"
    );
}

/// Double-revocation: revoking an already-revoked token is idempotent.
#[test]
fn test_double_revocation_idempotent() {
    let mut harness = quick_federation();

    // Revoke once.
    harness
        .federation_mut(0)
        .submit_revocation(0, "double-revoke");
    drive_to_finalization(&mut harness, 0, 5).unwrap();

    // Revoke again (same token ID).
    harness
        .federation_mut(0)
        .submit_revocation(1, "double-revoke");
    drive_to_finalization(&mut harness, 0, 5).unwrap();

    // Should still be revoked, no error.
    let fed = harness.federation(0);
    assert!(fed.is_revoked(0, "double-revoke"));

    // State should be consistent.
    harness.assert_all_nodes_agree(0);
}
