//! Negation proof integration tests: non-membership and temporal absence.
//!
//! Tests the circuit primitives for proving negative claims:
//! 1. Non-membership: "user NOT in suspended set"
//! 2. Temporal absence: "attribute NOT held during interval"

use pyana_circuit::field::BabyBear;
use pyana_circuit::non_membership::{
    NonMembershipProver, SetIdentifier, verify_non_membership_proof,
};
use pyana_circuit::poseidon2::hash_many;
use pyana_circuit::temporal_absence_air::{
    TIMELINE_DEPTH, TemporalAbsenceWitness, TimelineEntry, build_timeline_tree,
    prove_temporal_absence, verify_temporal_absence,
};
use pyana_dsl_runtime::temporal_absence::{
    DslTimelineEntry, TemporalAbsenceDslWitness, prove_temporal_absence_dsl,
    verify_temporal_absence_dsl,
};

// ─── Helpers ─────────────────────────────────────────────────────────────────

/// Derive a hash for a user ID.
fn user_hash(user_id: u32) -> BabyBear {
    hash_many(&[BabyBear::new(user_id), BabyBear::new(0xFACE)])
}

/// Build a timeline from events and return (root, entries).
fn build_test_timeline(entries: &[(u32, BabyBear, BabyBear)]) -> (BabyBear, Vec<TimelineEntry>) {
    let leaf_hashes: Vec<BabyBear> = entries
        .iter()
        .enumerate()
        .map(|(i, (bh, et, ah))| {
            hash_many(&[BabyBear::new(*bh), *et, *ah, BabyBear::new(i as u32)])
        })
        .collect();

    let (root, paths) = build_timeline_tree(&leaf_hashes);

    let timeline_entries: Vec<TimelineEntry> = entries
        .iter()
        .enumerate()
        .map(|(i, (bh, et, ah))| {
            let mut merkle_path = paths[i].clone();
            merkle_path.resize(TIMELINE_DEPTH, BabyBear::ZERO);
            TimelineEntry {
                block_height: *bh,
                event_type: *et,
                attribute_hash: *ah,
                timeline_index: i as u32,
                merkle_path,
            }
        })
        .collect();

    (root, timeline_entries)
}

// ─── Non-membership tests ────────────────────────────────────────────────────

/// Happy path: prove user NOT in suspended set, then add user, prove again fails.
#[test]
fn test_non_membership_prove_then_add_user_fails() {
    let suspended_set: Vec<BabyBear> = (1..=5).map(|i| user_hash(i * 100)).collect();
    let set_id = SetIdentifier::new("suspended_users");

    // User 42 is NOT in the suspended set.
    let user_42 = user_hash(42);
    assert!(!suspended_set.contains(&user_42));

    // Phase 1: prove non-membership successfully.
    let prover = NonMembershipProver::with_set_id(&suspended_set, set_id.clone());
    let proof = prover
        .prove_non_membership(&[user_42])
        .expect("User 42 is NOT suspended, proof should succeed");
    assert!(
        prover.verify_non_membership(&proof).is_ok(),
        "Non-membership proof should verify"
    );

    // Phase 2: add user 42 to the suspended set.
    let mut updated_set = suspended_set.clone();
    updated_set.push(user_42);

    // Phase 3: attempt to prove non-membership again — MUST fail.
    let prover_updated = NonMembershipProver::with_set_id(&updated_set, set_id);
    let result = prover_updated.prove_non_membership(&[user_42]);
    assert!(
        result.is_none(),
        "Should NOT be able to prove non-membership for a user that was added to the set"
    );
}

/// Adversarial: tamper with the proof accumulator → verification fails.
#[test]
fn test_non_membership_tampered_proof_rejected() {
    let suspended_set: Vec<BabyBear> = (1..=10).map(|i| user_hash(i * 50)).collect();
    let prover =
        NonMembershipProver::with_set_id(&suspended_set, SetIdentifier::new("tamper_test"));

    let user = user_hash(9999);
    let mut proof = prover
        .prove_non_membership(&[user])
        .expect("Should produce proof for non-member");

    // Tamper with the accumulator value.
    proof.accumulator.0[0] = BabyBear::new(0xDEAD);
    proof.accumulator.0[1] = BabyBear::new(0xBEEF);

    // Verification with tampered proof should fail.
    let result = verify_non_membership_proof(&proof);
    assert!(
        result.is_err(),
        "Tampered accumulator should cause verification failure"
    );
}

/// Adversarial: cross-set replay — proof from set A does not verify against set B.
#[test]
fn test_non_membership_cross_set_replay_rejected() {
    let set_a: Vec<BabyBear> = (1..=5).map(|i| user_hash(i * 10)).collect();
    let set_b: Vec<BabyBear> = (100..=105).map(|i| user_hash(i * 10)).collect();

    let prover_a = NonMembershipProver::with_set_id(&set_a, SetIdentifier::new("set_alpha"));
    let prover_b = NonMembershipProver::with_set_id(&set_b, SetIdentifier::new("set_beta"));

    let user = user_hash(9999);

    // Generate proof from set A.
    let proof_from_a = prover_a
        .prove_non_membership(&[user])
        .expect("Should prove non-membership in set A");

    // This proof is valid for set A's prover.
    assert!(prover_a.verify_non_membership(&proof_from_a).is_ok());

    // But it should NOT verify against set B (different accumulator/alpha).
    let result = prover_b.verify_non_membership(&proof_from_a);
    assert!(
        result.is_err(),
        "Cross-set replay should be rejected: proof from set A must not verify under set B"
    );
}

/// Multiple users: prove several users are NOT in the set at once.
#[test]
fn test_non_membership_batch_prove() {
    let blacklist: Vec<BabyBear> = (1..=20).map(|i| user_hash(i)).collect();
    let prover = NonMembershipProver::with_set_id(&blacklist, SetIdentifier::new("blacklist"));

    // Multiple users not in the blacklist.
    let users: Vec<BabyBear> = (100..=104).map(|i| user_hash(i)).collect();
    for u in &users {
        assert!(!blacklist.contains(u));
    }

    let proof = prover
        .prove_non_membership(&users)
        .expect("Should prove batch non-membership");
    assert!(prover.verify_non_membership(&proof).is_ok());
}

/// Edge case: empty set — any user trivially has non-membership.
#[test]
fn test_non_membership_empty_set() {
    let empty_set: Vec<BabyBear> = vec![];
    let prover = NonMembershipProver::with_set_id(&empty_set, SetIdentifier::new("empty"));

    let user = user_hash(42);
    let proof = prover
        .prove_non_membership(&[user])
        .expect("Non-membership in empty set should always succeed");
    assert!(prover.verify_non_membership(&proof).is_ok());
}

// ─── Temporal absence tests ──────────────────────────────────────────────────

/// Happy path: prove attribute NOT held during interval [11, 49].
#[test]
fn test_temporal_absence_valid_gap_proof() {
    let attr_x = BabyBear::new(0xDEAD);
    let attr_y = BabyBear::new(0xBEEF);
    let event_type = BabyBear::new(1);

    // Timeline: events at blocks 5, 10, 50, 100 — all for attr_y, NOT attr_x.
    let entries = vec![
        (5u32, event_type, attr_y),
        (10, event_type, attr_y),
        (50, event_type, attr_y),
        (100, event_type, attr_y),
    ];

    let (root, timeline) = build_test_timeline(&entries);

    // Gap between index 1 (block 10) and index 2 (block 50) covers [11, 49].
    let witness = TemporalAbsenceWitness {
        entry_before: timeline[1].clone(),
        entry_after: timeline[2].clone(),
        t1: 11,
        t2: 49,
        excluded_attribute_hash: attr_x,
        timeline_root: root,
    };

    assert!(witness.is_valid(), "Witness should be valid");

    let proof = prove_temporal_absence(&witness).expect("Should generate temporal absence proof");
    let valid = verify_temporal_absence(&proof, 11, 49, attr_x, root);
    assert!(valid, "Temporal absence proof should verify");
}

/// Adversarial: non-adjacent entries — attempt to skip an event → fails.
#[test]
fn test_temporal_absence_non_adjacent_fails() {
    let attr_x = BabyBear::new(0xDEAD);
    let attr_y = BabyBear::new(0xBEEF);
    let event_type = BabyBear::new(1);

    // Timeline has an event at block 30 (index 2) that we try to skip.
    let entries = vec![
        (5u32, event_type, attr_y),
        (10, event_type, attr_y),
        (30, event_type, attr_x), // attr_x event AT block 30 within our gap!
        (50, event_type, attr_y),
        (100, event_type, attr_y),
    ];

    let (root, timeline) = build_test_timeline(&entries);

    // Dishonest witness: try to use entries at index 1 (block 10) and index 3 (block 50).
    // These are NOT adjacent (index 2 exists between them).
    let witness = TemporalAbsenceWitness {
        entry_before: timeline[1].clone(),
        entry_after: timeline[3].clone(),
        t1: 11,
        t2: 49,
        excluded_attribute_hash: attr_x,
        timeline_root: root,
    };

    assert!(
        !witness.is_valid(),
        "Non-adjacent entries should produce invalid witness"
    );
    let proof = prove_temporal_absence(&witness);
    assert!(
        proof.is_none(),
        "Should NOT generate proof from invalid witness"
    );
}

/// Adversarial: verify with wrong parameters is rejected.
#[test]
fn test_temporal_absence_wrong_params_rejected() {
    let attr_x = BabyBear::new(0xDEAD);
    let attr_y = BabyBear::new(0xBEEF);
    let event_type = BabyBear::new(1);

    let entries = vec![
        (5u32, event_type, attr_y),
        (10, event_type, attr_y),
        (50, event_type, attr_y),
        (100, event_type, attr_y),
    ];

    let (root, timeline) = build_test_timeline(&entries);

    let witness = TemporalAbsenceWitness {
        entry_before: timeline[1].clone(),
        entry_after: timeline[2].clone(),
        t1: 11,
        t2: 49,
        excluded_attribute_hash: attr_x,
        timeline_root: root,
    };

    let proof = prove_temporal_absence(&witness).unwrap();

    // Correct parameters verify.
    assert!(verify_temporal_absence(&proof, 11, 49, attr_x, root));

    // Wrong t1 → rejected.
    assert!(!verify_temporal_absence(&proof, 12, 49, attr_x, root));

    // Wrong t2 → rejected.
    assert!(!verify_temporal_absence(&proof, 11, 50, attr_x, root));

    // Wrong attribute → rejected.
    assert!(!verify_temporal_absence(
        &proof,
        11,
        49,
        BabyBear::new(0xCAFE),
        root
    ));

    // Wrong timeline root → rejected.
    assert!(!verify_temporal_absence(
        &proof,
        11,
        49,
        attr_x,
        BabyBear::new(1)
    ));
}

/// Adversarial: timing constraint violation — entry_before is AFTER t1.
#[test]
fn test_temporal_absence_entry_before_after_t1_fails() {
    let attr_x = BabyBear::new(0xDEAD);
    let attr_y = BabyBear::new(0xBEEF);
    let event_type = BabyBear::new(1);

    let entries = vec![
        (5u32, event_type, attr_y),
        (20, event_type, attr_y), // block 20
        (50, event_type, attr_y),
        (100, event_type, attr_y),
    ];

    let (root, timeline) = build_test_timeline(&entries);

    // Claim t1 = 15, but entry_before is at block 20 > 15.
    let witness = TemporalAbsenceWitness {
        entry_before: timeline[1].clone(), // block 20 > t1=15
        entry_after: timeline[2].clone(),
        t1: 15,
        t2: 49,
        excluded_attribute_hash: attr_x,
        timeline_root: root,
    };

    assert!(
        !witness.is_valid(),
        "entry_before after t1 should produce invalid witness"
    );
    assert!(prove_temporal_absence(&witness).is_none());
}

/// Exact boundary case: entry_before.block_height == t1, entry_after.block_height == t2.
#[test]
fn test_temporal_absence_exact_boundaries() {
    let attr_x = BabyBear::new(0xDEAD);
    let attr_y = BabyBear::new(0xBEEF);
    let event_type = BabyBear::new(1);

    let entries = vec![
        (5u32, event_type, attr_y),
        (10, event_type, attr_y),
        (50, event_type, attr_y),
        (100, event_type, attr_y),
    ];

    let (root, timeline) = build_test_timeline(&entries);

    // Exactly at boundaries: t1=10 (entry_before at 10), t2=50 (entry_after at 50).
    let witness = TemporalAbsenceWitness {
        entry_before: timeline[1].clone(),
        entry_after: timeline[2].clone(),
        t1: 10,
        t2: 50,
        excluded_attribute_hash: attr_x,
        timeline_root: root,
    };

    assert!(witness.is_valid(), "Exact boundary should be valid");
    let proof = prove_temporal_absence(&witness).unwrap();
    assert!(verify_temporal_absence(&proof, 10, 50, attr_x, root));
}

// ─── DSL-native temporal absence tests ──────────────────────────────────────

/// DSL-native temporal absence proof: valid gap between adjacent entries.
#[test]
fn test_temporal_absence_dsl_valid_gap() {
    let attr_x = BabyBear::new(0xDEAD);
    let attr_y = BabyBear::new(0xBEEF);
    let event_type = BabyBear::new(1);

    // Build timeline using the old infrastructure (for Merkle root computation).
    let entries = vec![
        (5u32, event_type, attr_y),
        (10, event_type, attr_y),
        (50, event_type, attr_y),
        (100, event_type, attr_y),
    ];

    let (root, _timeline) = build_test_timeline(&entries);

    // Build DSL witness (uses simplified trace without Merkle path in AIR).
    let entry_before = DslTimelineEntry {
        block_height: 10,
        event_type,
        attribute_hash: attr_y,
        timeline_index: 1,
        merkle_root: root,
    };
    let entry_after = DslTimelineEntry {
        block_height: 50,
        event_type,
        attribute_hash: attr_y,
        timeline_index: 2,
        merkle_root: root,
    };

    let dsl_witness = TemporalAbsenceDslWitness {
        entry_before,
        entry_after,
        t1: 11,
        t2: 49,
        excluded_attribute_hash: attr_x,
    };

    assert!(dsl_witness.is_valid(), "DSL witness should be valid");

    let proof = prove_temporal_absence_dsl(&dsl_witness)
        .expect("Should generate DSL temporal absence proof");
    assert!(
        verify_temporal_absence_dsl(&proof, 11, 49, attr_x, root),
        "DSL temporal absence proof should verify"
    );
}

/// DSL-native: wrong parameters rejected.
#[test]
fn test_temporal_absence_dsl_wrong_params_rejected() {
    let attr_x = BabyBear::new(0xDEAD);
    let attr_y = BabyBear::new(0xBEEF);
    let event_type = BabyBear::new(1);

    let entries = vec![
        (5u32, event_type, attr_y),
        (10, event_type, attr_y),
        (50, event_type, attr_y),
        (100, event_type, attr_y),
    ];

    let (root, _timeline) = build_test_timeline(&entries);

    let dsl_witness = TemporalAbsenceDslWitness {
        entry_before: DslTimelineEntry {
            block_height: 10,
            event_type,
            attribute_hash: attr_y,
            timeline_index: 1,
            merkle_root: root,
        },
        entry_after: DslTimelineEntry {
            block_height: 50,
            event_type,
            attribute_hash: attr_y,
            timeline_index: 2,
            merkle_root: root,
        },
        t1: 11,
        t2: 49,
        excluded_attribute_hash: attr_x,
    };

    let proof = prove_temporal_absence_dsl(&dsl_witness).unwrap();

    // Correct params verify.
    assert!(verify_temporal_absence_dsl(&proof, 11, 49, attr_x, root));

    // Wrong t1
    assert!(!verify_temporal_absence_dsl(&proof, 12, 49, attr_x, root));
    // Wrong t2
    assert!(!verify_temporal_absence_dsl(&proof, 11, 50, attr_x, root));
    // Wrong attribute
    assert!(!verify_temporal_absence_dsl(
        &proof,
        11,
        49,
        BabyBear::new(0xCAFE),
        root
    ));
    // Wrong root
    assert!(!verify_temporal_absence_dsl(
        &proof,
        11,
        49,
        attr_x,
        BabyBear::new(1)
    ));
}
