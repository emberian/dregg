//! Comprehensive tests for the persistent store.
//!
//! Tests cover: CRUD for each storage type, recovery after simulated restart,
//! concurrent access safety, edge cases, and integrity checking.

use crate::federation::{PublicKey, Signature, StoredAttestedRoot};
use crate::{PersistentStore, StoreError};

// =============================================================================
// Helpers
// =============================================================================

fn new_store() -> PersistentStore {
    PersistentStore::open_in_memory().expect("failed to open in-memory store")
}

fn sample_attested_root(height: u64) -> StoredAttestedRoot {
    StoredAttestedRoot {
        merkle_root: [height as u8; 32],
        note_tree_root: None,
        nullifier_set_root: None,
        height,
        timestamp: 1000 + height as i64 * 100,
        blocklace_block_id: None,
        finality_round: None,
        quorum_signatures: vec![
            (PublicKey([0x11; 32]), Signature([0x22; 64])),
            (PublicKey([0x33; 32]), Signature([0x44; 64])),
            (PublicKey([0x55; 32]), Signature([0x66; 64])),
        ],
        threshold_qc: None,
        threshold: 2,
        federation_id: dregg_types::FederationId::PLACEHOLDER,
        receipt_stream_root: None,
    }
}

// =============================================================================
// Federation (Revocation) Tests
// =============================================================================

#[test]
fn revocation_store_and_check() {
    let store = new_store();

    assert!(!store.is_revoked("token-1").unwrap());
    store.store_revocation("token-1").unwrap();
    assert!(store.is_revoked("token-1").unwrap());
    assert!(!store.is_revoked("token-2").unwrap());
}

#[test]
fn revocation_idempotent() {
    let store = new_store();

    store.store_revocation("token-1").unwrap();
    store.store_revocation("token-1").unwrap(); // Should not error.
    assert_eq!(store.revocation_count().unwrap(), 1);
}

#[test]
fn revocation_count() {
    let store = new_store();

    assert_eq!(store.revocation_count().unwrap(), 0);
    store.store_revocation("a").unwrap();
    store.store_revocation("b").unwrap();
    store.store_revocation("c").unwrap();
    assert_eq!(store.revocation_count().unwrap(), 3);
}

#[test]
fn revocation_list() {
    let store = new_store();

    store.store_revocation("beta").unwrap();
    store.store_revocation("alpha").unwrap();
    store.store_revocation("gamma").unwrap();

    let mut list = store.list_revocations().unwrap();
    list.sort();
    assert_eq!(list, vec!["alpha", "beta", "gamma"]);
}

#[test]
fn revocation_batch() {
    let store = new_store();

    let count = store
        .store_revocations_batch(&["x", "y", "z", "x"])
        .unwrap();
    // "x" appears twice but should only be counted once.
    assert_eq!(count, 3);
    assert_eq!(store.revocation_count().unwrap(), 3);
    assert!(store.is_revoked("x").unwrap());
    assert!(store.is_revoked("y").unwrap());
    assert!(store.is_revoked("z").unwrap());
}

#[test]
fn revocation_time() {
    let store = new_store();

    store.store_revocation_at("token-1", 1234567890).unwrap();
    assert_eq!(store.revocation_time("token-1").unwrap(), Some(1234567890));
    assert_eq!(store.revocation_time("token-2").unwrap(), None);
}

// =============================================================================
// Federation (Attested Root) Tests
// =============================================================================

/// DIAGNOSIS — the N3 committee-restart hole (`node/src/blocklace_sync.rs`
/// full-mode commit path).
///
/// The commit path persists a full-mode attested root with only the LOCAL
/// node's single signature and `threshold = committee size`. On restart,
/// `verify_signed_anchor_and_rollback` (`node/src/state.rs`) calls
/// [`StoredAttestedRoot::verify_signatures`], which requires
/// `quorum_signatures.len() >= threshold` valid committee signatures over the
/// root's canonical `signing_message()`. A single-signature root therefore
/// fails and a full-mode committee node fail-closes after finalizing >=1
/// height (solo/threshold-1 is unaffected).
///
/// This test PINS both halves of the CORRECT recovery-anchor behavior so the
/// eventual fix is measured against the right bar (and so the anchor is never
/// silently weakened):
///   * a genuinely sub-quorum root (1 sig, threshold 3) is REFUSED — the
///     recovery anchor is correct security hardening and must stay strict;
///   * a genuine committee quorum (>=threshold valid sigs over the SAME
///     message) is ACCEPTED — exactly the record the persistence layer must
///     produce to close the hole WITHOUT relaxing the check;
///   * a quorum-COUNT of signatures that do not verify over this root's
///     message (they signed a different merkle_root) is still REFUSED — the
///     anchor binds the committed state root, not just a signature count.
#[test]
fn full_mode_single_sig_root_is_refused_genuine_quorum_accepted() {
    use dregg_types::{SigningKey, sign};

    // A 3-member committee (the N3 full-mode shape); threshold = 3.
    let sks: Vec<SigningKey> = (1u8..=3)
        .map(|s| SigningKey::from_bytes(&[s; 32]))
        .collect();
    let committee: Vec<PublicKey> = sks.iter().map(|k| k.public_key()).collect();

    // Build the attested root the way the full-mode commit path does.
    let mut root = StoredAttestedRoot {
        merkle_root: [0xAB; 32],
        note_tree_root: None,
        nullifier_set_root: None,
        height: 1,
        timestamp: 1_700_000_000,
        blocklace_block_id: Some([0xCD; 32]),
        finality_round: Some(1),
        quorum_signatures: Vec::new(),
        threshold_qc: None,
        threshold: 3,
        federation_id: dregg_types::FederationId::PLACEHOLDER,
        receipt_stream_root: Some([0xEF; 32]),
    };
    let msg = root.signing_message();

    // ── THE BUG: full mode persists ONLY the local signature. 1 < 3. ──
    root.quorum_signatures = vec![(committee[0], sign(&sks[0], &msg))];
    assert!(
        !root.verify_signatures(&committee),
        "a single-signature full-mode root MUST be refused on restart — the \
         recovery anchor is correct; the persistence under-feeds it (N3 hole)"
    );

    // ── THE FIX TARGET: a genuine committee quorum over the SAME message. ──
    root.quorum_signatures = sks
        .iter()
        .map(|k| (k.public_key(), sign(k, &msg)))
        .collect();
    assert!(
        root.verify_signatures(&committee),
        "a genuine >=threshold committee quorum over the root's signing message \
         MUST be accepted — this is the record the commit path must persist"
    );

    // ── The anchor stays strict against forgery: >=threshold signatures that
    //    do NOT verify over THIS root's message (they signed a different
    //    merkle_root) are still refused. ──
    let other = StoredAttestedRoot {
        merkle_root: [0x00; 32],
        ..root.clone()
    };
    let other_msg = other.signing_message();
    root.quorum_signatures = sks
        .iter()
        .map(|k| (k.public_key(), sign(k, &other_msg)))
        .collect();
    assert!(
        !root.verify_signatures(&committee),
        "three signatures over a DIFFERENT merkle_root must NOT satisfy the \
         anchor — the check binds the committed state root, not just a count"
    );
}

#[test]
fn attested_root_store_and_load() {
    let store = new_store();

    let root = sample_attested_root(1);
    store.store_attested_root(&root).unwrap();

    let loaded = store.latest_attested_root().unwrap();
    assert_eq!(loaded, Some(root));
}

#[test]
fn attested_root_latest_tracks_highest() {
    let store = new_store();

    store.store_attested_root(&sample_attested_root(1)).unwrap();
    store.store_attested_root(&sample_attested_root(5)).unwrap();
    store.store_attested_root(&sample_attested_root(3)).unwrap();

    // Latest should be height 5 (highest stored).
    let latest = store.latest_attested_root().unwrap().unwrap();
    assert_eq!(latest.height, 5);
}

#[test]
fn attested_root_by_height() {
    let store = new_store();

    let root3 = sample_attested_root(3);
    store.store_attested_root(&root3).unwrap();

    let loaded = store.attested_root_at_height(3).unwrap();
    assert_eq!(loaded, Some(root3));
    assert_eq!(store.attested_root_at_height(99).unwrap(), None);
}

#[test]
fn attested_root_empty() {
    let store = new_store();
    assert_eq!(store.latest_attested_root().unwrap(), None);
    assert_eq!(store.attested_root_count().unwrap(), 0);
}

#[test]
fn attested_root_count() {
    let store = new_store();

    store.store_attested_root(&sample_attested_root(1)).unwrap();
    store.store_attested_root(&sample_attested_root(2)).unwrap();
    store.store_attested_root(&sample_attested_root(3)).unwrap();
    assert_eq!(store.attested_root_count().unwrap(), 3);
}

#[test]
fn attested_root_all_ordered() {
    let store = new_store();

    store.store_attested_root(&sample_attested_root(3)).unwrap();
    store.store_attested_root(&sample_attested_root(1)).unwrap();
    store.store_attested_root(&sample_attested_root(2)).unwrap();

    let all = store.all_attested_roots().unwrap();
    assert_eq!(all.len(), 3);
    // Should be in height order (redb stores u64 keys in order).
    assert_eq!(all[0].height, 1);
    assert_eq!(all[1].height, 2);
    assert_eq!(all[2].height, 3);
}

#[test]
fn attested_root_validity() {
    let root = sample_attested_root(1);
    assert!(root.is_structurally_complete()); // 3 sigs >= threshold 2.

    let invalid = StoredAttestedRoot {
        threshold: 5,
        ..root
    };
    assert!(!invalid.is_structurally_complete()); // 3 sigs < threshold 5.
}

// =============================================================================
// Edge Cases
// =============================================================================

#[test]
fn many_revocations() {
    let store = new_store();

    let ids: Vec<String> = (0..1000).map(|i| format!("token-{i:05}")).collect();
    let refs: Vec<&str> = ids.iter().map(|s| s.as_str()).collect();
    store.store_revocations_batch(&refs).unwrap();

    assert_eq!(store.revocation_count().unwrap(), 1000);
    assert!(store.is_revoked("token-00500").unwrap());
    assert!(!store.is_revoked("token-01000").unwrap());
}

#[test]
fn store_root_hex() {
    let root = sample_attested_root(0xAB);
    // Height 0xAB = 171, so merkle_root = [171; 32].
    assert_eq!(root.root_hex(), "abababab");
}

// =============================================================================
// Note Tree & Nullifier Tests
// =============================================================================

#[test]
fn test_store_note_roundtrip() {
    use dregg_cell::note::Note;

    let store = new_store();

    // Create notes with deterministic randomness.
    let note1 = Note::with_randomness([1u8; 32], [1, 100, 0, 0, 0, 0, 0, 0], [10u8; 32]);
    let note2 = Note::with_randomness([2u8; 32], [1, 200, 0, 0, 0, 0, 0, 0], [20u8; 32]);
    let note3 = Note::with_randomness([3u8; 32], [2, 50, 0, 0, 0, 0, 0, 0], [30u8; 32]);

    let c1 = note1.commitment();
    let c2 = note2.commitment();
    let c3 = note3.commitment();

    // Store commitments.
    let pos1 = store.store_note_commitment(&c1).unwrap();
    let pos2 = store.store_note_commitment(&c2).unwrap();
    let pos3 = store.store_note_commitment(&c3).unwrap();

    assert_eq!(pos1, 0);
    assert_eq!(pos2, 1);
    assert_eq!(pos3, 2);
    assert_eq!(store.note_count().unwrap(), 3);

    // Recover and verify tree root matches.
    let commitments = store.load_all_note_commitments().unwrap();
    assert_eq!(commitments.len(), 3);
    assert_eq!(commitments[0], c1);
    assert_eq!(commitments[1], c2);
    assert_eq!(commitments[2], c3);

    // Rebuild tree and check root.
    let mut tree = crate::note_tree::NoteTree::from_commitments(commitments);
    let root = tree.root();
    let stored_root = store.note_tree_root().unwrap();
    assert_eq!(root, stored_root);
}

#[test]
fn test_nullifier_persistence() {
    use dregg_cell::note::{Note, Nullifier};

    let store = new_store();
    let note = Note::with_randomness([1u8; 32], [1, 100, 0, 0, 0, 0, 0, 0], [10u8; 32]);
    let spending_key = [0xBB; 32];
    let nullifier = note.nullifier(&spending_key);

    // Not spent initially.
    assert!(!store.is_nullifier_spent(&nullifier).unwrap());

    // Store it.
    store.store_nullifier(&nullifier).unwrap();

    // Now it's spent.
    assert!(store.is_nullifier_spent(&nullifier).unwrap());

    // Double-spend is rejected.
    let result = store.store_nullifier(&nullifier);
    assert!(matches!(result, Err(StoreError::Integrity(_))));

    // A different nullifier is not spent.
    let other_nullifier = Nullifier([0xFF; 32]);
    assert!(!store.is_nullifier_spent(&other_nullifier).unwrap());
}

#[test]
fn test_nullifier_persistence_across_restart() {
    use dregg_cell::note::Note;

    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("note_test.redb");
    let note = Note::with_randomness([1u8; 32], [1, 100, 0, 0, 0, 0, 0, 0], [10u8; 32]);
    let spending_key = [0xBB; 32];
    let nullifier = note.nullifier(&spending_key);

    // First session: store commitment and nullifier.
    {
        let store = PersistentStore::open(&path).unwrap();
        store.store_note_commitment(&note.commitment()).unwrap();
        store.store_nullifier(&nullifier).unwrap();
    }

    // Second session: verify persistence.
    {
        let store = PersistentStore::open(&path).unwrap();
        assert_eq!(store.note_count().unwrap(), 1);
        assert!(store.is_nullifier_spent(&nullifier).unwrap());

        let commitments = store.load_all_note_commitments().unwrap();
        assert_eq!(commitments[0], note.commitment());
    }
}

#[test]
fn test_spend_note_atomic() {
    use dregg_cell::note::Note;

    let store = new_store();

    let note1 = Note::with_randomness([1u8; 32], [1, 100, 0, 0, 0, 0, 0, 0], [10u8; 32]);
    let note2 = Note::with_randomness([2u8; 32], [1, 200, 0, 0, 0, 0, 0, 0], [20u8; 32]);
    let spending_key = [0xBB; 32];

    // First: store the original commitment for note1 (simulate issuance).
    store.store_note_commitment(&note1.commitment()).unwrap();
    assert_eq!(store.note_count().unwrap(), 1);

    // Spend note1 atomically: insert its nullifier + store the output commitment (note2).
    let nullifier1 = note1.nullifier(&spending_key);
    let pos = store
        .spend_note_atomic(&nullifier1, &note2.commitment())
        .unwrap();
    assert_eq!(pos, 1); // Second commitment is at position 1.

    // Verify both side effects occurred.
    assert!(store.is_nullifier_spent(&nullifier1).unwrap());
    assert_eq!(store.note_count().unwrap(), 2);

    // Double-spend is rejected atomically.
    let note3 = Note::with_randomness([3u8; 32], [2, 50, 0, 0, 0, 0, 0, 0], [30u8; 32]);
    let result = store.spend_note_atomic(&nullifier1, &note3.commitment());
    assert!(matches!(result, Err(StoreError::Integrity(_))));

    // The failed double-spend must not have added the commitment.
    assert_eq!(store.note_count().unwrap(), 2);
}

#[test]
fn test_spend_note_atomic_double_spend_no_side_effects() {
    use dregg_cell::note::Note;

    let store = new_store();

    let note1 = Note::with_randomness([1u8; 32], [1, 100, 0, 0, 0, 0, 0, 0], [10u8; 32]);
    let note2 = Note::with_randomness([2u8; 32], [1, 200, 0, 0, 0, 0, 0, 0], [20u8; 32]);
    let note3 = Note::with_randomness([3u8; 32], [2, 50, 0, 0, 0, 0, 0, 0], [30u8; 32]);
    let spending_key = [0xBB; 32];
    let nullifier1 = note1.nullifier(&spending_key);

    // Spend note1 successfully (creating note2 as output).
    let pos = store
        .spend_note_atomic(&nullifier1, &note2.commitment())
        .unwrap();
    assert_eq!(pos, 0);
    assert_eq!(store.note_count().unwrap(), 1);

    // Attempt double-spend: should fail AND not add note3's commitment.
    let result = store.spend_note_atomic(&nullifier1, &note3.commitment());
    assert!(result.is_err());
    assert_eq!(store.note_count().unwrap(), 1); // Still 1, not 2.
}

#[test]
fn test_attested_root_includes_note_tree() {
    use dregg_cell::note::Note;

    let store = new_store();

    // Add some notes.
    let note1 = Note::with_randomness([1u8; 32], [1, 100, 0, 0, 0, 0, 0, 0], [10u8; 32]);
    let note2 = Note::with_randomness([2u8; 32], [1, 200, 0, 0, 0, 0, 0, 0], [20u8; 32]);
    store.store_note_commitment(&note1.commitment()).unwrap();
    store.store_note_commitment(&note2.commitment()).unwrap();

    // Add a nullifier.
    let spending_key = [0xBB; 32];
    let nullifier = note1.nullifier(&spending_key);
    store.store_nullifier(&nullifier).unwrap();

    // Get the roots.
    let note_root = store.note_tree_root().unwrap();
    let nullifier_root = store.nullifier_set_root().unwrap();

    // Both should be non-zero (non-empty sets).
    assert_ne!(note_root, [0u8; 32]);
    assert_ne!(nullifier_root, [0u8; 32]);

    // Create an attested root that includes all three components.
    let attested = StoredAttestedRoot {
        merkle_root: [0xAB; 32], // Cell state root.
        note_tree_root: Some(note_root),
        nullifier_set_root: Some(nullifier_root),
        height: 1,
        timestamp: 1700000000,
        blocklace_block_id: None,
        finality_round: None,
        quorum_signatures: vec![(PublicKey([0x11; 32]), Signature([0x22; 64]))],
        threshold_qc: None,
        threshold: 1,
        federation_id: dregg_types::FederationId::PLACEHOLDER,
        receipt_stream_root: None,
    };

    // Store and recover.
    store.store_attested_root(&attested).unwrap();
    let loaded = store.latest_attested_root().unwrap().unwrap();
    assert_eq!(loaded.note_tree_root, Some(note_root));
    assert_eq!(loaded.nullifier_set_root, Some(nullifier_root));
    assert_eq!(loaded.merkle_root, [0xAB; 32]);
}

// =============================================================================
// Forever-Digest Set Tests (restart-durable anti-replay carriers)
// =============================================================================

#[test]
fn forever_digests_survive_reopen() {
    use crate::tables::{NS_COURT_RESOLVED, NS_TRUSTLINE_DIGEST};

    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("forever.redb");

    let scope = [0x11; 32];
    let draw = [0x22; 32];
    let resolved = [0x33; 32];

    {
        let store = PersistentStore::open(&path).expect("open store");
        assert!(
            store
                .record_forever_digest(NS_TRUSTLINE_DIGEST, &scope, &draw)
                .unwrap(),
            "first burn is new"
        );
        assert!(
            !store
                .record_forever_digest(NS_TRUSTLINE_DIGEST, &scope, &draw)
                .unwrap(),
            "second burn is idempotent"
        );
        assert!(
            store
                .record_forever_digest(NS_COURT_RESOLVED, &[0u8; 32], &resolved)
                .unwrap()
        );
        // Drop: the simulated restart.
    }

    let store = PersistentStore::open(&path).expect("reopen store");
    assert!(
        store
            .forever_digest_seen(NS_TRUSTLINE_DIGEST, &scope, &draw)
            .unwrap(),
        "a burned draw digest survives the restart"
    );
    assert!(
        store
            .forever_digest_seen(NS_COURT_RESOLVED, &[0u8; 32], &resolved)
            .unwrap(),
        "a resolved-evidence digest survives the restart"
    );

    // Namespaces do not bleed: the same bytes under the other namespace are unseen.
    assert!(
        !store
            .forever_digest_seen(NS_COURT_RESOLVED, &scope, &draw)
            .unwrap()
    );
    assert!(
        !store
            .forever_digest_seen(NS_TRUSTLINE_DIGEST, &[0u8; 32], &resolved)
            .unwrap()
    );

    // Boot-time load returns exactly the namespace's pairs.
    let trustline_pairs = store.load_forever_digests(NS_TRUSTLINE_DIGEST).unwrap();
    assert_eq!(trustline_pairs, vec![(scope, draw)]);
    let court_pairs = store.load_forever_digests(NS_COURT_RESOLVED).unwrap();
    assert_eq!(court_pairs, vec![([0u8; 32], resolved)]);
}

#[test]
fn forever_digest_scopes_are_disjoint() {
    use crate::tables::NS_TRUSTLINE_DIGEST;

    let store = new_store();
    let digest = [0x77; 32];
    store
        .record_forever_digest(NS_TRUSTLINE_DIGEST, &[0xAA; 32], &digest)
        .unwrap();
    assert!(
        !store
            .forever_digest_seen(NS_TRUSTLINE_DIGEST, &[0xBB; 32], &digest)
            .unwrap(),
        "a digest burned against one trustline does not refuse another's"
    );
}

// =============================================================================
// Durable Channel Roster Tests (docs/PERSISTENCE.md §3, the roster caveat)
// =============================================================================

#[test]
fn channel_rosters_roundtrip_and_survive_reopen() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("rosters.redb");

    let channel_a = [0xA1; 32];
    let channel_b = [0xB2; 32];
    let roster_a = vec![1u8, 2, 3, 4];
    let roster_a2 = vec![9u8, 8, 7];
    let roster_b = vec![5u8, 6];

    {
        let store = PersistentStore::open(&path).expect("open store");
        store.store_channel_roster(&channel_a, &roster_a).unwrap();
        store.store_channel_roster(&channel_b, &roster_b).unwrap();
        // Upsert: a later epoch step overwrites.
        store.store_channel_roster(&channel_a, &roster_a2).unwrap();
        // Drop: the simulated restart.
    }

    let store = PersistentStore::open(&path).expect("reopen store");
    let mut loaded = store.load_channel_rosters().unwrap();
    loaded.sort();
    assert_eq!(
        loaded,
        vec![
            (channel_a, roster_a2.clone()),
            (channel_b, roster_b.clone())
        ]
    );

    // A stale roster's discard is durable.
    store.remove_channel_roster(&channel_a).unwrap();
    let loaded = store.load_channel_rosters().unwrap();
    assert_eq!(loaded, vec![(channel_b, roster_b)]);
}
