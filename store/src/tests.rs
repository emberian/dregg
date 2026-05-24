//! Comprehensive tests for the persistent store.
//!
//! Tests cover: CRUD for each storage type, recovery after simulated restart,
//! concurrent access safety, edge cases, and integrity checking.

use crate::audit::{AuditEventType, StoredAuditEvent};
use crate::federation::{PublicKey, Signature, StoredAttestedRoot};
use crate::tokens::{StoredFoldStep, TokenChain};
use crate::{PersistentStore, StoreError};

// =============================================================================
// Helpers
// =============================================================================

fn new_store() -> PersistentStore {
    PersistentStore::open_in_memory().expect("failed to open in-memory store")
}

fn sample_token_chain() -> TokenChain {
    TokenChain {
        initial_root: [0x01; 32],
        steps: vec![
            StoredFoldStep {
                old_root: [0x01; 32],
                new_root: [0x02; 32],
                delta_bytes: vec![0xDE, 0xAD, 0xBE, 0xEF],
                timestamp: 1000,
            },
            StoredFoldStep {
                old_root: [0x02; 32],
                new_root: [0x03; 32],
                delta_bytes: vec![0xCA, 0xFE],
                timestamp: 2000,
            },
        ],
        current_root: [0x03; 32],
        issuer_key: [0xAA; 32],
        created_at: 500,
    }
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
        federation_id: pyana_types::FederationId::PLACEHOLDER,
    }
}

fn sample_audit_event(token_id: [u8; 32], event_type: AuditEventType) -> StoredAuditEvent {
    StoredAuditEvent {
        token_id,
        event_type,
        timestamp: 1700000000,
        action_hash: [0xBB; 32],
        actor: [0xCC; 32],
        sequence: 0, // Will be assigned on append.
        metadata: vec![1, 2, 3],
    }
}

// =============================================================================
// Token Chain Tests
// =============================================================================

#[test]
fn token_chain_store_and_load() {
    let store = new_store();
    let token_id = [0x42; 32];
    let chain = sample_token_chain();

    store.store_token_chain(&token_id, &chain).unwrap();

    let loaded = store.load_token_chain(&token_id).unwrap();
    assert_eq!(loaded, Some(chain));
}

#[test]
fn token_chain_load_nonexistent() {
    let store = new_store();
    let token_id = [0xFF; 32];

    let loaded = store.load_token_chain(&token_id).unwrap();
    assert_eq!(loaded, None);
}

#[test]
fn token_chain_overwrite() {
    let store = new_store();
    let token_id = [0x42; 32];

    let chain1 = sample_token_chain();
    store.store_token_chain(&token_id, &chain1).unwrap();

    let chain2 = TokenChain {
        initial_root: [0xFF; 32],
        steps: vec![],
        current_root: [0xFF; 32],
        issuer_key: [0xBB; 32],
        created_at: 9999,
    };
    store.store_token_chain(&token_id, &chain2).unwrap();

    let loaded = store.load_token_chain(&token_id).unwrap();
    assert_eq!(loaded, Some(chain2));
}

#[test]
fn token_chain_list_tokens() {
    let store = new_store();

    assert_eq!(store.list_tokens().unwrap(), Vec::<[u8; 32]>::new());

    let id1 = [0x01; 32];
    let id2 = [0x02; 32];
    let id3 = [0x03; 32];

    let chain = sample_token_chain();
    store.store_token_chain(&id1, &chain).unwrap();
    store.store_token_chain(&id2, &chain).unwrap();
    store.store_token_chain(&id3, &chain).unwrap();

    let mut tokens = store.list_tokens().unwrap();
    tokens.sort();
    assert_eq!(tokens.len(), 3);
    assert!(tokens.contains(&id1));
    assert!(tokens.contains(&id2));
    assert!(tokens.contains(&id3));
}

#[test]
fn token_chain_delete() {
    let store = new_store();
    let token_id = [0x42; 32];
    let chain = sample_token_chain();

    store.store_token_chain(&token_id, &chain).unwrap();
    assert!(store.delete_token_chain(&token_id).unwrap());
    assert!(!store.delete_token_chain(&token_id).unwrap());
    assert_eq!(store.load_token_chain(&token_id).unwrap(), None);
}

#[test]
fn token_chain_count() {
    let store = new_store();
    assert_eq!(store.token_count().unwrap(), 0);

    let chain = sample_token_chain();
    store.store_token_chain(&[0x01; 32], &chain).unwrap();
    store.store_token_chain(&[0x02; 32], &chain).unwrap();
    assert_eq!(store.token_count().unwrap(), 2);
}

#[test]
fn token_chain_append_fold_step() {
    let store = new_store();
    let token_id = [0x42; 32];

    let chain = sample_token_chain();
    store.store_token_chain(&token_id, &chain).unwrap();

    let new_step = StoredFoldStep {
        old_root: [0x03; 32], // Matches chain.current_root.
        new_root: [0x04; 32],
        delta_bytes: vec![0x11, 0x22],
        timestamp: 3000,
    };
    store.append_fold_step(&token_id, new_step.clone()).unwrap();

    let loaded = store.load_token_chain(&token_id).unwrap().unwrap();
    assert_eq!(loaded.current_root, [0x04; 32]);
    assert_eq!(loaded.steps.len(), 3);
    assert_eq!(loaded.steps[2], new_step);
}

#[test]
fn token_chain_append_fold_step_bad_continuity() {
    let store = new_store();
    let token_id = [0x42; 32];

    let chain = sample_token_chain();
    store.store_token_chain(&token_id, &chain).unwrap();

    let bad_step = StoredFoldStep {
        old_root: [0xFF; 32], // Does NOT match chain.current_root.
        new_root: [0x04; 32],
        delta_bytes: vec![],
        timestamp: 3000,
    };
    let result = store.append_fold_step(&token_id, bad_step);
    assert!(matches!(result, Err(StoreError::Integrity(_))));
}

#[test]
fn token_chain_append_fold_step_nonexistent() {
    let store = new_store();
    let token_id = [0xFF; 32];

    let step = StoredFoldStep {
        old_root: [0x01; 32],
        new_root: [0x02; 32],
        delta_bytes: vec![],
        timestamp: 1000,
    };
    let result = store.append_fold_step(&token_id, step);
    assert!(matches!(result, Err(StoreError::NotFound)));
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
// Key Management Tests
// =============================================================================

#[test]
fn signing_key_store_and_load() {
    let store = new_store();
    let key = [0x42; 32];
    let master = [0xAA; 32];

    store
        .store_signing_key("authority-1", &key, &master)
        .unwrap();
    let loaded = store.load_signing_key("authority-1", &master).unwrap();
    assert_eq!(loaded, Some(key));
}

#[test]
fn signing_key_wrong_master() {
    let store = new_store();
    let key = [0x42; 32];
    let master = [0xAA; 32];
    let wrong_master = [0xBB; 32];

    store
        .store_signing_key("authority-1", &key, &master)
        .unwrap();
    let result = store.load_signing_key("authority-1", &wrong_master);
    assert!(matches!(result, Err(StoreError::Crypto(_))));
}

#[test]
fn signing_key_nonexistent() {
    let store = new_store();
    let master = [0xAA; 32];
    let loaded = store.load_signing_key("nope", &master).unwrap();
    assert_eq!(loaded, None);
}

#[test]
fn signing_key_delete() {
    let store = new_store();
    let key = [0x42; 32];
    let master = [0xAA; 32];

    store
        .store_signing_key("authority-1", &key, &master)
        .unwrap();
    assert!(store.delete_signing_key("authority-1").unwrap());
    assert!(!store.delete_signing_key("authority-1").unwrap());
    assert_eq!(
        store.load_signing_key("authority-1", &master).unwrap(),
        None
    );
}

#[test]
fn signing_key_list() {
    let store = new_store();
    let master = [0xAA; 32];

    store.store_signing_key("alpha", &[1; 32], &master).unwrap();
    store.store_signing_key("beta", &[2; 32], &master).unwrap();
    store.store_signing_key("gamma", &[3; 32], &master).unwrap();

    let mut names = store.list_signing_keys().unwrap();
    names.sort();
    assert_eq!(names, vec!["alpha", "beta", "gamma"]);
}

#[test]
fn signing_key_overwrite() {
    let store = new_store();
    let master = [0xAA; 32];

    store
        .store_signing_key("key", &[0x11; 32], &master)
        .unwrap();
    store
        .store_signing_key("key", &[0x22; 32], &master)
        .unwrap();

    let loaded = store.load_signing_key("key", &master).unwrap();
    assert_eq!(loaded, Some([0x22; 32]));
}

#[test]
fn signing_key_different_names_independent() {
    let store = new_store();
    let master = [0xAA; 32];

    store
        .store_signing_key("key-a", &[0x11; 32], &master)
        .unwrap();
    store
        .store_signing_key("key-b", &[0x22; 32], &master)
        .unwrap();

    assert_eq!(
        store.load_signing_key("key-a", &master).unwrap(),
        Some([0x11; 32])
    );
    assert_eq!(
        store.load_signing_key("key-b", &master).unwrap(),
        Some([0x22; 32])
    );
}

#[test]
fn public_key_store_and_load() {
    let store = new_store();
    let key = [0x77; 32];

    store.store_public_key("node-1", &key).unwrap();
    let loaded = store.load_public_key("node-1").unwrap();
    assert_eq!(loaded, Some(key));
}

#[test]
fn public_key_nonexistent() {
    let store = new_store();
    assert_eq!(store.load_public_key("nope").unwrap(), None);
}

#[test]
fn public_key_delete() {
    let store = new_store();
    store.store_public_key("node-1", &[0x77; 32]).unwrap();
    assert!(store.delete_public_key("node-1").unwrap());
    assert!(!store.delete_public_key("node-1").unwrap());
}

#[test]
fn public_key_list() {
    let store = new_store();

    store.store_public_key("node-a", &[1; 32]).unwrap();
    store.store_public_key("node-b", &[2; 32]).unwrap();

    let mut names = store.list_public_keys().unwrap();
    names.sort();
    assert_eq!(names, vec!["node-a", "node-b"]);
}

#[test]
fn key_existence_checks() {
    let store = new_store();
    let master = [0xAA; 32];

    assert!(!store.has_signing_key("x").unwrap());
    assert!(!store.has_public_key("x").unwrap());

    store.store_signing_key("x", &[1; 32], &master).unwrap();
    store.store_public_key("x", &[2; 32]).unwrap();

    assert!(store.has_signing_key("x").unwrap());
    assert!(store.has_public_key("x").unwrap());
}

// =============================================================================
// Audit Log Tests
// =============================================================================

#[test]
fn audit_append_and_get() {
    let store = new_store();
    let event = sample_audit_event([0x42; 32], AuditEventType::TokenPresented);

    let seq = store.append_audit_event(&event).unwrap();
    assert_eq!(seq, 0);

    let loaded = store.get_audit_event(0).unwrap().unwrap();
    assert_eq!(loaded.token_id, event.token_id);
    assert_eq!(loaded.event_type, event.event_type);
    assert_eq!(loaded.sequence, 0);
}

#[test]
fn audit_sequential_numbering() {
    let store = new_store();

    let event = sample_audit_event([0x42; 32], AuditEventType::TokenPresented);

    let s0 = store.append_audit_event(&event).unwrap();
    let s1 = store.append_audit_event(&event).unwrap();
    let s2 = store.append_audit_event(&event).unwrap();

    assert_eq!(s0, 0);
    assert_eq!(s1, 1);
    assert_eq!(s2, 2);
    assert_eq!(store.audit_count().unwrap(), 3);
}

#[test]
fn audit_get_nonexistent() {
    let store = new_store();
    assert_eq!(store.get_audit_event(999).unwrap(), None);
}

#[test]
fn audit_count_empty() {
    let store = new_store();
    assert_eq!(store.audit_count().unwrap(), 0);
}

#[test]
fn audit_events_for_token() {
    let store = new_store();

    let token_a = [0xAA; 32];
    let token_b = [0xBB; 32];

    store
        .append_audit_event(&sample_audit_event(token_a, AuditEventType::TokenIssued))
        .unwrap();
    store
        .append_audit_event(&sample_audit_event(token_b, AuditEventType::TokenIssued))
        .unwrap();
    store
        .append_audit_event(&sample_audit_event(token_a, AuditEventType::TokenPresented))
        .unwrap();
    store
        .append_audit_event(&sample_audit_event(
            token_a,
            AuditEventType::TokenAttenuated,
        ))
        .unwrap();
    store
        .append_audit_event(&sample_audit_event(token_b, AuditEventType::TokenRevoked))
        .unwrap();

    let a_events = store.audit_events_for_token(&token_a).unwrap();
    assert_eq!(a_events.len(), 3);
    assert_eq!(a_events[0].event_type, AuditEventType::TokenIssued);
    assert_eq!(a_events[1].event_type, AuditEventType::TokenPresented);
    assert_eq!(a_events[2].event_type, AuditEventType::TokenAttenuated);

    let b_events = store.audit_events_for_token(&token_b).unwrap();
    assert_eq!(b_events.len(), 2);
}

#[test]
fn audit_events_for_unknown_token() {
    let store = new_store();
    store
        .append_audit_event(&sample_audit_event([0xAA; 32], AuditEventType::TokenIssued))
        .unwrap();

    let events = store.audit_events_for_token(&[0xFF; 32]).unwrap();
    assert!(events.is_empty());
}

#[test]
fn audit_events_range() {
    let store = new_store();

    for i in 0..10 {
        let mut event = sample_audit_event([0x42; 32], AuditEventType::TokenPresented);
        event.timestamp = 1000 + i;
        store.append_audit_event(&event).unwrap();
    }

    let range = store.audit_events_range(3, 7).unwrap();
    assert_eq!(range.len(), 4);
    assert_eq!(range[0].sequence, 3);
    assert_eq!(range[3].sequence, 6);
}

#[test]
fn audit_latest_events() {
    let store = new_store();

    for i in 0..10 {
        let mut event = sample_audit_event([0x42; 32], AuditEventType::TokenPresented);
        event.timestamp = 1000 + i;
        store.append_audit_event(&event).unwrap();
    }

    let latest = store.latest_audit_events(3).unwrap();
    assert_eq!(latest.len(), 3);
    // Most recent first.
    assert_eq!(latest[0].sequence, 9);
    assert_eq!(latest[1].sequence, 8);
    assert_eq!(latest[2].sequence, 7);
}

#[test]
fn audit_latest_events_more_than_available() {
    let store = new_store();

    store
        .append_audit_event(&sample_audit_event([0x42; 32], AuditEventType::TokenIssued))
        .unwrap();

    let latest = store.latest_audit_events(100).unwrap();
    assert_eq!(latest.len(), 1);
}

#[test]
fn audit_batch_append() {
    let store = new_store();

    let events: Vec<StoredAuditEvent> = (0..5)
        .map(|i| {
            let mut e = sample_audit_event([0x42; 32], AuditEventType::TokenPresented);
            e.timestamp = 1000 + i;
            e
        })
        .collect();

    let first_seq = store.append_audit_events_batch(&events).unwrap();
    assert_eq!(first_seq, 0);
    assert_eq!(store.audit_count().unwrap(), 5);

    for i in 0..5 {
        let e = store.get_audit_event(i).unwrap().unwrap();
        assert_eq!(e.sequence, i);
    }
}

#[test]
fn audit_event_types() {
    let store = new_store();

    let types = vec![
        AuditEventType::TokenPresented,
        AuditEventType::TokenAttenuated,
        AuditEventType::TokenRevoked,
        AuditEventType::TokenIssued,
        AuditEventType::KeyOperation,
        AuditEventType::ConsensusEvent,
        AuditEventType::Custom("my_event".to_string()),
    ];

    for t in &types {
        store
            .append_audit_event(&sample_audit_event([0x42; 32], t.clone()))
            .unwrap();
    }

    for (i, t) in types.iter().enumerate() {
        let loaded = store.get_audit_event(i as u64).unwrap().unwrap();
        assert_eq!(&loaded.event_type, t);
    }
}

// =============================================================================
// Recovery Tests
// =============================================================================

#[test]
fn recovery_empty_store() {
    let store = new_store();
    let state = store.recover_federation_state().unwrap();

    assert!(state.revoked_tokens.is_empty());
    assert!(state.latest_root.is_none());
    assert_eq!(state.token_count, 0);
    assert_eq!(state.audit_count, 0);
    assert_eq!(state.revocation_count, 0);
    assert_eq!(state.attested_root_count, 0);
}

#[test]
fn recovery_populated_store() {
    let store = new_store();

    // Populate some data.
    store.store_revocation("rev-1").unwrap();
    store.store_revocation("rev-2").unwrap();
    store.store_attested_root(&sample_attested_root(5)).unwrap();
    store
        .store_token_chain(&[0x01; 32], &sample_token_chain())
        .unwrap();
    store
        .append_audit_event(&sample_audit_event([0x01; 32], AuditEventType::TokenIssued))
        .unwrap();

    let state = store.recover_federation_state().unwrap();
    assert_eq!(state.revocation_count, 2);
    assert!(state.revoked_tokens.contains(&"rev-1".to_string()));
    assert!(state.revoked_tokens.contains(&"rev-2".to_string()));
    assert_eq!(state.latest_root.unwrap().height, 5);
    assert_eq!(state.token_count, 1);
    assert_eq!(state.audit_count, 1);
    assert_eq!(state.attested_root_count, 1);
}

#[test]
fn recovery_simulated_restart_file_based() {
    // Use a temp file to simulate restart.
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("test.redb");

    // First "session": write data.
    {
        let store = PersistentStore::open(&path).unwrap();
        store.store_revocation("revoked-token-1").unwrap();
        store.store_revocation("revoked-token-2").unwrap();
        store
            .store_attested_root(&sample_attested_root(10))
            .unwrap();
        store
            .store_token_chain(&[0xAB; 32], &sample_token_chain())
            .unwrap();
        store
            .append_audit_event(&sample_audit_event([0xAB; 32], AuditEventType::TokenIssued))
            .unwrap();
        store
            .append_audit_event(&sample_audit_event(
                [0xAB; 32],
                AuditEventType::TokenPresented,
            ))
            .unwrap();
        // Store drops here, simulating process exit.
    }

    // Second "session": recover.
    {
        let store = PersistentStore::open(&path).unwrap();
        let state = store.recover_federation_state().unwrap();

        assert_eq!(state.revocation_count, 2);
        assert!(
            state
                .revoked_tokens
                .contains(&"revoked-token-1".to_string())
        );
        assert!(
            state
                .revoked_tokens
                .contains(&"revoked-token-2".to_string())
        );
        assert_eq!(state.latest_root.unwrap().height, 10);
        assert_eq!(state.token_count, 1);
        assert_eq!(state.audit_count, 2);

        // Verify the token chain survived.
        let chain = store.load_token_chain(&[0xAB; 32]).unwrap().unwrap();
        assert_eq!(chain.steps.len(), 2);
        assert_eq!(chain.current_root, [0x03; 32]);

        // Verify audit events.
        let events = store.audit_events_for_token(&[0xAB; 32]).unwrap();
        assert_eq!(events.len(), 2);
        assert_eq!(events[0].event_type, AuditEventType::TokenIssued);
        assert_eq!(events[1].event_type, AuditEventType::TokenPresented);
    }
}

// =============================================================================
// Integrity Check Tests
// =============================================================================

#[test]
fn integrity_check_clean_store() {
    let store = new_store();

    // Add some consistent data.
    store
        .store_token_chain(&[0x01; 32], &sample_token_chain())
        .unwrap();
    store.store_attested_root(&sample_attested_root(1)).unwrap();
    store
        .append_audit_event(&sample_audit_event([0x01; 32], AuditEventType::TokenIssued))
        .unwrap();

    let report = store.check_integrity().unwrap();
    assert!(report.is_ok());
    assert!(report.errors.is_empty());
}

#[test]
fn integrity_check_broken_chain() {
    let store = new_store();

    // Store a chain with bad continuity.
    let bad_chain = TokenChain {
        initial_root: [0x01; 32],
        steps: vec![
            StoredFoldStep {
                old_root: [0x01; 32],
                new_root: [0x02; 32],
                delta_bytes: vec![],
                timestamp: 1000,
            },
            StoredFoldStep {
                old_root: [0xFF; 32], // BAD: doesn't match previous new_root.
                new_root: [0x03; 32],
                delta_bytes: vec![],
                timestamp: 2000,
            },
        ],
        current_root: [0x03; 32],
        issuer_key: [0xAA; 32],
        created_at: 500,
    };

    store.store_token_chain(&[0x01; 32], &bad_chain).unwrap();

    let report = store.check_integrity().unwrap();
    assert!(!report.is_ok());
    assert!(!report.chain_continuity_ok);
    assert!(!report.errors.is_empty());
}

// =============================================================================
// Concurrent Access Tests
// =============================================================================

#[test]
fn concurrent_reads() {
    let store = new_store();
    let chain = sample_token_chain();
    store.store_token_chain(&[0x42; 32], &chain).unwrap();

    // Multiple reads should not conflict.
    for _ in 0..100 {
        let loaded = store.load_token_chain(&[0x42; 32]).unwrap();
        assert_eq!(loaded, Some(chain.clone()));
    }
}

#[test]
fn interleaved_operations() {
    let store = new_store();

    // Mix different table operations.
    store.store_revocation("r1").unwrap();
    store
        .store_token_chain(&[0x01; 32], &sample_token_chain())
        .unwrap();
    store
        .append_audit_event(&sample_audit_event([0x01; 32], AuditEventType::TokenIssued))
        .unwrap();
    store.store_public_key("pk1", &[0x77; 32]).unwrap();
    store.store_attested_root(&sample_attested_root(1)).unwrap();

    // Verify all stored correctly.
    assert!(store.is_revoked("r1").unwrap());
    assert!(store.load_token_chain(&[0x01; 32]).unwrap().is_some());
    assert_eq!(store.audit_count().unwrap(), 1);
    assert_eq!(store.load_public_key("pk1").unwrap(), Some([0x77; 32]));
    assert!(store.latest_attested_root().unwrap().is_some());
}

// =============================================================================
// Edge Cases
// =============================================================================

#[test]
fn empty_token_chain() {
    let store = new_store();
    let chain = TokenChain {
        initial_root: [0xFF; 32],
        steps: vec![],
        current_root: [0xFF; 32],
        issuer_key: [0xAA; 32],
        created_at: 0,
    };

    store.store_token_chain(&[0x01; 32], &chain).unwrap();
    let loaded = store.load_token_chain(&[0x01; 32]).unwrap();
    assert_eq!(loaded, Some(chain));
}

#[test]
fn large_delta_bytes() {
    let store = new_store();

    let large_delta = vec![0xAB; 1024 * 64]; // 64 KB delta.
    let chain = TokenChain {
        initial_root: [0x01; 32],
        steps: vec![StoredFoldStep {
            old_root: [0x01; 32],
            new_root: [0x02; 32],
            delta_bytes: large_delta.clone(),
            timestamp: 1000,
        }],
        current_root: [0x02; 32],
        issuer_key: [0xAA; 32],
        created_at: 500,
    };

    store.store_token_chain(&[0x01; 32], &chain).unwrap();
    let loaded = store.load_token_chain(&[0x01; 32]).unwrap().unwrap();
    assert_eq!(loaded.steps[0].delta_bytes.len(), 1024 * 64);
}

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
fn many_audit_events() {
    let store = new_store();

    let events: Vec<StoredAuditEvent> = (0..500)
        .map(|i| {
            let mut e = sample_audit_event([0x42; 32], AuditEventType::TokenPresented);
            e.timestamp = 1000 + i;
            e
        })
        .collect();

    store.append_audit_events_batch(&events).unwrap();
    assert_eq!(store.audit_count().unwrap(), 500);

    let token_events = store.audit_events_for_token(&[0x42; 32]).unwrap();
    assert_eq!(token_events.len(), 500);
}

#[test]
fn audit_event_with_metadata() {
    let store = new_store();

    let mut event = sample_audit_event([0x42; 32], AuditEventType::Custom("test".to_string()));
    event.metadata = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    store.append_audit_event(&event).unwrap();

    let loaded = store.get_audit_event(0).unwrap().unwrap();
    assert_eq!(loaded.metadata, vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
    assert_eq!(
        loaded.event_type,
        AuditEventType::Custom("test".to_string())
    );
}

#[test]
fn signing_key_all_zeros() {
    let store = new_store();
    let key = [0x00; 32];
    let master = [0x00; 32];

    // Even all-zeros should work (edge case for XOR encryption).
    store.store_signing_key("zero", &key, &master).unwrap();
    let loaded = store.load_signing_key("zero", &master).unwrap();
    assert_eq!(loaded, Some(key));
}

#[test]
fn signing_key_all_ones() {
    let store = new_store();
    let key = [0xFF; 32];
    let master = [0xFF; 32];

    store.store_signing_key("ones", &key, &master).unwrap();
    let loaded = store.load_signing_key("ones", &master).unwrap();
    assert_eq!(loaded, Some(key));
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
    use pyana_cell::note::Note;

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
    use pyana_cell::note::{Note, Nullifier};

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
    use pyana_cell::note::Note;

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
    use pyana_cell::note::{Note, Nullifier};

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
    use pyana_cell::note::Note;

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
    use pyana_cell::note::Note;

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
        federation_id: pyana_types::FederationId::PLACEHOLDER,
    };

    // Store and recover.
    store.store_attested_root(&attested).unwrap();
    let loaded = store.latest_attested_root().unwrap().unwrap();
    assert_eq!(loaded.note_tree_root, Some(note_root));
    assert_eq!(loaded.nullifier_set_root, Some(nullifier_root));
    assert_eq!(loaded.merkle_root, [0xAB; 32]);
}
