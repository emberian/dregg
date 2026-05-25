use crate::capability::{CapabilityRef, CapabilitySet};
use crate::cell::{Cell, VerificationKey};
use crate::id::CellId;
use crate::ledger::{CellStateDelta, Ledger, LedgerDelta, LedgerError};
use crate::permissions::{Action, AuthKind, AuthRequired, Permissions};
use crate::preconditions::{
    CellStatePrecondition, EvalContext, NetworkPrecondition, PreconditionError, Preconditions,
    TimeRange,
};
use crate::state::{CellState, FIELD_ZERO, STATE_SLOTS};

// ============================================================
// Helper functions
// ============================================================

fn test_key(seed: u8) -> [u8; 32] {
    let mut key = [0u8; 32];
    key[0] = seed;
    key[31] = seed.wrapping_mul(37);
    key
}

fn test_token(seed: u8) -> [u8; 32] {
    let mut token = [0u8; 32];
    token[0] = seed;
    token[1] = 0xAA;
    token
}

fn field_from_u64(val: u64) -> [u8; 32] {
    let mut f = [0u8; 32];
    f[24..32].copy_from_slice(&val.to_be_bytes());
    f
}

// ============================================================
// CellId tests
// ============================================================

#[test]
fn cell_id_derive_deterministic() {
    let pk = test_key(1);
    let token = test_token(1);
    let id1 = CellId::derive_raw(&pk, &token);
    let id2 = CellId::derive_raw(&pk, &token);
    assert_eq!(id1, id2);
}

#[test]
fn cell_id_different_keys_different_ids() {
    let token = test_token(1);
    let id1 = CellId::derive_raw(&test_key(1), &token);
    let id2 = CellId::derive_raw(&test_key(2), &token);
    assert_ne!(id1, id2);
}

#[test]
fn cell_id_different_tokens_different_ids() {
    let pk = test_key(1);
    let id1 = CellId::derive_raw(&pk, &test_token(1));
    let id2 = CellId::derive_raw(&pk, &test_token(2));
    assert_ne!(id1, id2);
}

#[test]
fn cell_id_from_bytes_roundtrip() {
    let pk = test_key(42);
    let token = test_token(99);
    let id = CellId::derive_raw(&pk, &token);
    let bytes = *id.as_bytes();
    let id2 = CellId::from_bytes(bytes);
    assert_eq!(id, id2);
}

#[test]
fn cell_id_display_debug() {
    let id = CellId::derive_raw(&test_key(1), &test_token(1));
    let display = format!("{id}");
    let debug = format!("{id:?}");
    assert!(!display.is_empty());
    assert!(debug.contains("CellId("));
}

#[test]
fn cell_id_zero_is_zero() {
    assert_eq!(CellId::ZERO.as_bytes(), &[0u8; 32]);
}

// ============================================================
// CellState tests
// ============================================================

#[test]
fn cell_state_new_has_correct_balance() {
    let state = CellState::new(1000);
    assert_eq!(state.balance, 1000);
    assert_eq!(state.nonce, 0);
    assert_eq!(state.fields, [FIELD_ZERO; STATE_SLOTS]);
}

#[test]
fn cell_state_set_field_valid() {
    let mut state = CellState::new(0);
    let value = field_from_u64(42);
    assert!(state.set_field(3, value));
    assert_eq!(state.get_field(3), Some(&value));
}

#[test]
fn cell_state_set_field_out_of_bounds() {
    let mut state = CellState::new(0);
    assert!(!state.set_field(8, field_from_u64(1)));
    assert!(!state.set_field(100, field_from_u64(1)));
}

#[test]
fn cell_state_get_field_out_of_bounds() {
    let state = CellState::new(0);
    assert_eq!(state.get_field(8), None);
}

#[test]
fn cell_state_increment_nonce() {
    let mut state = CellState::new(0);
    assert_eq!(state.nonce, 0);
    assert!(state.increment_nonce());
    assert_eq!(state.nonce, 1);
    assert!(state.increment_nonce());
    assert_eq!(state.nonce, 2);
}

#[test]
fn cell_state_balance_add() {
    let mut state = CellState::new(100);
    assert!(state.apply_balance_change(50));
    assert_eq!(state.balance, 150);
}

#[test]
fn cell_state_balance_subtract() {
    let mut state = CellState::new(100);
    assert!(state.apply_balance_change(-30));
    assert_eq!(state.balance, 70);
}

#[test]
fn cell_state_balance_underflow() {
    let mut state = CellState::new(10);
    assert!(!state.apply_balance_change(-20));
    // Balance unchanged on failure.
    assert_eq!(state.balance, 10);
}

#[test]
fn cell_state_balance_overflow() {
    let mut state = CellState::new(u64::MAX - 5);
    assert!(!state.apply_balance_change(10));
    assert_eq!(state.balance, u64::MAX - 5);
}

// ============================================================
// Permissions tests
// ============================================================

#[test]
fn auth_required_none_always_satisfied() {
    assert!(AuthRequired::None.is_satisfied_by(&AuthKind::Signature));
    assert!(AuthRequired::None.is_satisfied_by(&AuthKind::Proof));
}

#[test]
fn auth_required_signature_only_sig() {
    assert!(AuthRequired::Signature.is_satisfied_by(&AuthKind::Signature));
    assert!(!AuthRequired::Signature.is_satisfied_by(&AuthKind::Proof));
}

#[test]
fn auth_required_proof_only_proof() {
    assert!(!AuthRequired::Proof.is_satisfied_by(&AuthKind::Signature));
    assert!(AuthRequired::Proof.is_satisfied_by(&AuthKind::Proof));
}

#[test]
fn auth_required_either_accepts_both() {
    assert!(AuthRequired::Either.is_satisfied_by(&AuthKind::Signature));
    assert!(AuthRequired::Either.is_satisfied_by(&AuthKind::Proof));
}

#[test]
fn auth_required_impossible_never_satisfied() {
    assert!(!AuthRequired::Impossible.is_satisfied_by(&AuthKind::Signature));
    assert!(!AuthRequired::Impossible.is_satisfied_by(&AuthKind::Proof));
}

#[test]
fn auth_narrower_or_equal_relations() {
    // Impossible is narrower than everything.
    assert!(AuthRequired::Impossible.is_narrower_or_equal(&AuthRequired::None));
    assert!(AuthRequired::Impossible.is_narrower_or_equal(&AuthRequired::Signature));
    assert!(AuthRequired::Impossible.is_narrower_or_equal(&AuthRequired::Proof));
    assert!(AuthRequired::Impossible.is_narrower_or_equal(&AuthRequired::Either));
    assert!(AuthRequired::Impossible.is_narrower_or_equal(&AuthRequired::Impossible));

    // None is NOT narrower than anything except None.
    assert!(AuthRequired::None.is_narrower_or_equal(&AuthRequired::None));
    assert!(!AuthRequired::None.is_narrower_or_equal(&AuthRequired::Signature));
    assert!(!AuthRequired::None.is_narrower_or_equal(&AuthRequired::Proof));

    // Signature/Proof are narrower than Either.
    assert!(AuthRequired::Signature.is_narrower_or_equal(&AuthRequired::Either));
    assert!(AuthRequired::Proof.is_narrower_or_equal(&AuthRequired::Either));

    // Signature is not narrower than Proof and vice versa.
    assert!(!AuthRequired::Signature.is_narrower_or_equal(&AuthRequired::Proof));
    assert!(!AuthRequired::Proof.is_narrower_or_equal(&AuthRequired::Signature));

    // Everything is narrower than or equal to None.
    assert!(AuthRequired::None.is_narrower_or_equal(&AuthRequired::None));
    assert!(AuthRequired::Signature.is_narrower_or_equal(&AuthRequired::None));
    assert!(AuthRequired::Proof.is_narrower_or_equal(&AuthRequired::None));
    assert!(AuthRequired::Either.is_narrower_or_equal(&AuthRequired::None));
}

#[test]
fn permissions_default_user_check() {
    let perms = Permissions::default_user();
    // Send requires signature.
    assert!(perms.check(Action::Send, &AuthKind::Signature));
    assert!(!perms.check(Action::Send, &AuthKind::Proof));
    // Receive requires nothing.
    assert!(perms.check(Action::Receive, &AuthKind::Signature));
    assert!(perms.check(Action::Receive, &AuthKind::Proof));
}

#[test]
fn permissions_zkapp_check() {
    let perms = Permissions::zkapp();
    // Send requires proof.
    assert!(!perms.check(Action::Send, &AuthKind::Signature));
    assert!(perms.check(Action::Send, &AuthKind::Proof));
}

#[test]
fn permissions_frozen_check() {
    let perms = Permissions::frozen();
    for action in [
        Action::Send,
        Action::Receive,
        Action::SetState,
        Action::SetPermissions,
        Action::SetVerificationKey,
        Action::IncrementNonce,
        Action::Delegate,
        Action::Access,
    ] {
        assert!(!perms.check(action, &AuthKind::Signature));
        assert!(!perms.check(action, &AuthKind::Proof));
    }
}

#[test]
fn permissions_for_action() {
    let perms = Permissions::default_user();
    assert_eq!(perms.for_action(Action::Send), &AuthRequired::Signature);
    assert_eq!(perms.for_action(Action::Receive), &AuthRequired::None);
}

// ============================================================
// Capability tests
// ============================================================

#[test]
fn capability_set_grant_and_lookup() {
    let mut caps = CapabilitySet::new();
    let target = CellId::derive_raw(&test_key(1), &test_token(1));
    let slot = caps.grant(target, AuthRequired::Signature).unwrap();
    assert_eq!(slot, 0);

    let cap = caps.lookup(slot).unwrap();
    assert_eq!(cap.target, target);
    assert_eq!(cap.permissions, AuthRequired::Signature);
    assert_eq!(cap.breadstuff, None);
}

#[test]
fn capability_set_grant_increments_slots() {
    let mut caps = CapabilitySet::new();
    let t1 = CellId::derive_raw(&test_key(1), &test_token(1));
    let t2 = CellId::derive_raw(&test_key(2), &test_token(1));

    let s1 = caps.grant(t1, AuthRequired::None).unwrap();
    let s2 = caps.grant(t2, AuthRequired::Proof).unwrap();
    assert_eq!(s1, 0);
    assert_eq!(s2, 1);
    assert_eq!(caps.len(), 2);
}

#[test]
fn capability_set_revoke() {
    let mut caps = CapabilitySet::new();
    let target = CellId::derive_raw(&test_key(1), &test_token(1));
    let slot = caps.grant(target, AuthRequired::None).unwrap();

    assert!(caps.revoke(slot));
    assert!(caps.lookup(slot).is_none());
    assert!(!caps.has_access(&target));
}

#[test]
fn capability_set_revoke_nonexistent() {
    let mut caps = CapabilitySet::new();
    assert!(!caps.revoke(99));
}

#[test]
fn capability_set_has_access() {
    let mut caps = CapabilitySet::new();
    let target = CellId::derive_raw(&test_key(5), &test_token(5));
    let other = CellId::derive_raw(&test_key(6), &test_token(6));

    caps.grant(target, AuthRequired::Signature);
    assert!(caps.has_access(&target));
    assert!(!caps.has_access(&other));
}

#[test]
fn capability_set_attenuate_valid() {
    let mut caps = CapabilitySet::new();
    let target = CellId::derive_raw(&test_key(1), &test_token(1));
    let slot = caps.grant(target, AuthRequired::Either).unwrap();

    // Attenuate from Either -> Signature (narrower).
    let attenuated = caps.attenuate(slot, AuthRequired::Signature);
    assert!(attenuated.is_some());
    let att = attenuated.unwrap();
    assert_eq!(att.permissions, AuthRequired::Signature);
    assert_eq!(att.target, target);
}

#[test]
fn capability_set_attenuate_to_impossible() {
    let mut caps = CapabilitySet::new();
    let target = CellId::derive_raw(&test_key(1), &test_token(1));
    let slot = caps.grant(target, AuthRequired::Signature).unwrap();

    // Attenuate to Impossible (always valid - most restrictive).
    let attenuated = caps.attenuate(slot, AuthRequired::Impossible);
    assert!(attenuated.is_some());
    assert_eq!(attenuated.unwrap().permissions, AuthRequired::Impossible);
}

#[test]
fn capability_set_attenuate_invalid_widening() {
    let mut caps = CapabilitySet::new();
    let target = CellId::derive_raw(&test_key(1), &test_token(1));
    let slot = caps.grant(target, AuthRequired::Signature).unwrap();

    // Can't widen from Signature to Either.
    let result = caps.attenuate(slot, AuthRequired::Either);
    assert!(result.is_none());

    // Can't widen from Signature to None.
    let result = caps.attenuate(slot, AuthRequired::None);
    assert!(result.is_none());
}

#[test]
fn capability_set_attenuate_nonexistent_slot() {
    let caps = CapabilitySet::new();
    assert!(caps.attenuate(0, AuthRequired::Signature).is_none());
}

#[test]
fn capability_set_with_breadstuff() {
    let mut caps = CapabilitySet::new();
    let target = CellId::derive_raw(&test_key(1), &test_token(1));
    let breadstuff = [0xBB; 32];
    let slot = caps
        .grant_with_breadstuff(target, AuthRequired::Proof, Some(breadstuff))
        .unwrap();

    let cap = caps.lookup(slot).unwrap();
    assert_eq!(cap.breadstuff, Some(breadstuff));
}

#[test]
fn capability_set_capabilities_for() {
    let mut caps = CapabilitySet::new();
    let target = CellId::derive_raw(&test_key(1), &test_token(1));
    let other = CellId::derive_raw(&test_key(2), &test_token(2));

    caps.grant(target, AuthRequired::None);
    caps.grant(target, AuthRequired::Signature);
    caps.grant(other, AuthRequired::Proof);

    let for_target = caps.capabilities_for(&target);
    assert_eq!(for_target.len(), 2);

    let for_other = caps.capabilities_for(&other);
    assert_eq!(for_other.len(), 1);
}

#[test]
fn capability_isolation_no_implicit_access() {
    let mut caps = CapabilitySet::new();
    let a = CellId::derive_raw(&test_key(1), &test_token(1));
    let b = CellId::derive_raw(&test_key(2), &test_token(2));
    let c = CellId::derive_raw(&test_key(3), &test_token(3));

    // Grant access only to A.
    caps.grant(a, AuthRequired::None);

    // B and C are not accessible.
    assert!(caps.has_access(&a));
    assert!(!caps.has_access(&b));
    assert!(!caps.has_access(&c));

    // Lookup by slot for non-granted targets returns None.
    assert!(caps.lookup(1).is_none());
    assert!(caps.lookup(99).is_none());
}

// ============================================================
// Cell tests
// ============================================================

#[test]
fn cell_new_derives_correct_id() {
    let pk = test_key(10);
    let token = test_token(20);
    let cell = Cell::new(pk, token);
    assert_eq!(cell.id, CellId::derive_raw(&pk, &token));
    assert_eq!(cell.public_key, pk);
    assert_eq!(cell.token_id, token);
    assert_eq!(cell.state.balance, 0);
    assert_eq!(cell.state.nonce, 0);
    assert!(cell.verification_key.is_none());
    assert!(cell.delegate.is_none());
    assert!(cell.capabilities.is_empty());
}

#[test]
fn cell_with_balance() {
    let cell = Cell::with_balance(test_key(1), test_token(1), 5000);
    assert_eq!(cell.state.balance, 5000);
}

#[test]
fn cell_spawn_child_sets_delegate() {
    let parent = Cell::new(test_key(1), test_token(1));
    let child = parent.spawn_child(test_key(2), test_token(2));
    assert_eq!(child.delegate, Some(parent.id));
    assert_ne!(child.id, parent.id);
}

#[test]
fn verification_key_hash_computed() {
    let data = vec![1, 2, 3, 4, 5];
    let vk = VerificationKey::new(data.clone());
    let expected_hash = *blake3::hash(&data).as_bytes();
    assert_eq!(vk.hash, expected_hash);
    assert_eq!(vk.data, data);
}

#[test]
fn verification_key_from_parts() {
    let hash = [0xAA; 32];
    let data = vec![10, 20, 30];
    let vk = VerificationKey::from_parts(hash, data.clone());
    assert_eq!(vk.hash, hash);
    assert_eq!(vk.data, data);
}

// ============================================================
// Ledger tests
// ============================================================

#[test]
fn ledger_new_is_empty() {
    let ledger = Ledger::new();
    assert!(ledger.is_empty());
    assert_eq!(ledger.len(), 0);
}

#[test]
fn ledger_create_cell() {
    let mut ledger = Ledger::new();
    let id = ledger.create_cell(test_key(1), test_token(1));
    assert_eq!(ledger.len(), 1);
    assert!(ledger.contains(&id));
    let cell = ledger.get(&id).unwrap();
    assert_eq!(cell.public_key, test_key(1));
}

#[test]
fn ledger_insert_cell_duplicate() {
    let mut ledger = Ledger::new();
    let cell = Cell::new(test_key(1), test_token(1));
    let id = cell.id;
    ledger.insert_cell(cell.clone()).unwrap();
    let err = ledger.insert_cell(cell).unwrap_err();
    assert_eq!(err, LedgerError::CellAlreadyExists(id));
}

#[test]
fn ledger_get_mut_modifies_cell() {
    let mut ledger = Ledger::new();
    let id = ledger.create_cell(test_key(1), test_token(1));
    {
        let cell = ledger.get_mut(&id).unwrap();
        cell.state.balance = 9999;
    }
    assert_eq!(ledger.get(&id).unwrap().state.balance, 9999);
}

#[test]
fn ledger_remove_cell() {
    let mut ledger = Ledger::new();
    let id = ledger.create_cell(test_key(1), test_token(1));
    assert!(ledger.contains(&id));
    let removed = ledger.remove(&id);
    assert!(removed.is_some());
    assert!(!ledger.contains(&id));
    assert_eq!(ledger.len(), 0);
}

#[test]
fn ledger_root_changes_on_mutation() {
    let mut ledger = Ledger::new();
    let root_empty = ledger.root();

    let id = ledger.create_cell(test_key(1), test_token(1));
    let root_one = ledger.root();
    assert_ne!(root_empty, root_one);

    ledger.create_cell(test_key(2), test_token(2));
    let root_two = ledger.root();
    assert_ne!(root_one, root_two);

    ledger.remove(&id);
    let root_after_remove = ledger.root();
    assert_ne!(root_two, root_after_remove);
}

#[test]
fn ledger_root_deterministic() {
    let mut l1 = Ledger::new();
    let mut l2 = Ledger::new();

    // Same operations in same order → same root.
    l1.create_cell(test_key(1), test_token(1));
    l1.create_cell(test_key(2), test_token(2));

    l2.create_cell(test_key(1), test_token(1));
    l2.create_cell(test_key(2), test_token(2));

    assert_eq!(l1.root(), l2.root());
}

#[test]
fn ledger_membership_proof_valid() {
    let mut ledger = Ledger::new();
    let id1 = ledger.create_cell(test_key(1), test_token(1));
    ledger.create_cell(test_key(2), test_token(2));
    ledger.create_cell(test_key(3), test_token(3));

    let proof = ledger.membership_proof(&id1).unwrap();
    assert_eq!(proof.cell_id, id1);
    assert_eq!(proof.root, ledger.root());
    assert!(proof.verify());
}

#[test]
fn ledger_membership_proof_single_cell() {
    let mut ledger = Ledger::new();
    let id = ledger.create_cell(test_key(1), test_token(1));

    let proof = ledger.membership_proof(&id).unwrap();
    assert!(proof.verify());
    // Single cell → the leaf IS the root (no siblings).
    assert!(proof.path.is_empty());
}

#[test]
fn ledger_membership_proof_nonexistent() {
    let mut ledger = Ledger::new();
    let id = CellId::derive_raw(&test_key(1), &test_token(1));
    assert!(ledger.membership_proof(&id).is_none());
}

#[test]
fn ledger_membership_proof_multiple_cells() {
    let mut ledger = Ledger::new();
    let ids: Vec<CellId> = (0..7)
        .map(|i| ledger.create_cell(test_key(i), test_token(i)))
        .collect();

    for id in &ids {
        let proof = ledger.membership_proof(id).unwrap();
        assert!(proof.verify(), "proof failed for cell {id}");
        assert_eq!(proof.root, ledger.root());
    }
}

// ============================================================
// LedgerDelta tests
// ============================================================

#[test]
fn ledger_delta_create_cells() {
    let mut ledger = Ledger::new();
    let cell1 = Cell::with_balance(test_key(1), test_token(1), 100);
    let cell2 = Cell::with_balance(test_key(2), test_token(2), 200);

    let delta = LedgerDelta {
        created: vec![cell1.clone(), cell2.clone()],
        updated: Vec::new(),
        computron_transfers: Vec::new(),
    };

    ledger.apply_delta(&delta).unwrap();
    assert_eq!(ledger.len(), 2);
    assert_eq!(ledger.get(&cell1.id).unwrap().state.balance, 100);
    assert_eq!(ledger.get(&cell2.id).unwrap().state.balance, 200);
}

#[test]
fn ledger_delta_create_duplicate_fails() {
    let mut ledger = Ledger::new();
    let cell = Cell::new(test_key(1), test_token(1));
    ledger.insert_cell(cell.clone()).unwrap();

    let delta = LedgerDelta {
        created: vec![cell.clone()],
        updated: Vec::new(),
        computron_transfers: Vec::new(),
    };

    let err = ledger.apply_delta(&delta).unwrap_err();
    assert_eq!(err, LedgerError::CellAlreadyExists(cell.id));
}

#[test]
fn ledger_delta_update_fields() {
    let mut ledger = Ledger::new();
    let id = ledger.create_cell(test_key(1), test_token(1));

    let new_field = field_from_u64(12345);
    let delta = LedgerDelta {
        created: Vec::new(),
        updated: vec![(
            id,
            CellStateDelta {
                field_updates: vec![(0, new_field), (7, field_from_u64(99))],
                nonce_increment: true,
                balance_change: 0,
                permission_changes: None,
                capability_grants: Vec::new(),
                capability_revocations: Vec::new(),
            },
        )],
        computron_transfers: Vec::new(),
    };

    ledger.apply_delta(&delta).unwrap();
    let cell = ledger.get(&id).unwrap();
    assert_eq!(cell.state.fields[0], new_field);
    assert_eq!(cell.state.fields[7], field_from_u64(99));
    assert_eq!(cell.state.nonce, 1);
}

#[test]
fn ledger_delta_update_nonexistent_cell_fails() {
    let mut ledger = Ledger::new();
    let fake_id = CellId::derive_raw(&test_key(99), &test_token(99));

    let delta = LedgerDelta {
        created: Vec::new(),
        updated: vec![(fake_id, CellStateDelta::empty())],
        computron_transfers: Vec::new(),
    };

    let err = ledger.apply_delta(&delta).unwrap_err();
    assert_eq!(err, LedgerError::CellNotFound(fake_id));
}

#[test]
fn ledger_delta_invalid_field_index_fails() {
    let mut ledger = Ledger::new();
    let id = ledger.create_cell(test_key(1), test_token(1));

    let delta = LedgerDelta {
        created: Vec::new(),
        updated: vec![(
            id,
            CellStateDelta {
                field_updates: vec![(STATE_SLOTS, field_from_u64(1))], // index 8 is invalid
                nonce_increment: false,
                balance_change: 0,
                permission_changes: None,
                capability_grants: Vec::new(),
                capability_revocations: Vec::new(),
            },
        )],
        computron_transfers: Vec::new(),
    };

    let err = ledger.apply_delta(&delta).unwrap_err();
    assert_eq!(
        err,
        LedgerError::InvalidFieldIndex {
            cell_id: id,
            index: STATE_SLOTS
        }
    );
}

#[test]
fn ledger_delta_balance_deduction_insufficient_fails() {
    let mut ledger = Ledger::new();
    let cell = Cell::with_balance(test_key(1), test_token(1), 50);
    let id = cell.id;
    ledger.insert_cell(cell).unwrap();

    let delta = LedgerDelta {
        created: Vec::new(),
        updated: vec![(
            id,
            CellStateDelta {
                field_updates: Vec::new(),
                nonce_increment: false,
                balance_change: -100,
                permission_changes: None,
                capability_grants: Vec::new(),
                capability_revocations: Vec::new(),
            },
        )],
        computron_transfers: Vec::new(),
    };

    let err = ledger.apply_delta(&delta).unwrap_err();
    assert_eq!(
        err,
        LedgerError::InsufficientBalance {
            cell_id: id,
            available: 50,
            required: 100,
        }
    );
}

#[test]
fn ledger_delta_computron_transfer() {
    let mut ledger = Ledger::new();
    let sender = Cell::with_balance(test_key(1), test_token(1), 1000);
    let receiver = Cell::with_balance(test_key(2), test_token(2), 500);
    let sender_id = sender.id;
    let receiver_id = receiver.id;
    ledger.insert_cell(sender).unwrap();
    ledger.insert_cell(receiver).unwrap();

    let delta = LedgerDelta {
        created: Vec::new(),
        updated: Vec::new(),
        computron_transfers: vec![(sender_id, receiver_id, 300)],
    };

    ledger.apply_delta(&delta).unwrap();
    assert_eq!(ledger.get(&sender_id).unwrap().state.balance, 700);
    assert_eq!(ledger.get(&receiver_id).unwrap().state.balance, 800);
}

#[test]
fn ledger_delta_transfer_insufficient_balance_fails() {
    let mut ledger = Ledger::new();
    let sender = Cell::with_balance(test_key(1), test_token(1), 100);
    let receiver = Cell::with_balance(test_key(2), test_token(2), 0);
    let sender_id = sender.id;
    let receiver_id = receiver.id;
    ledger.insert_cell(sender).unwrap();
    ledger.insert_cell(receiver).unwrap();

    let delta = LedgerDelta {
        created: Vec::new(),
        updated: Vec::new(),
        computron_transfers: vec![(sender_id, receiver_id, 200)],
    };

    let err = ledger.apply_delta(&delta).unwrap_err();
    assert_eq!(
        err,
        LedgerError::InsufficientBalance {
            cell_id: sender_id,
            available: 100,
            required: 200,
        }
    );
    // Ledger unchanged on failure.
    assert_eq!(ledger.get(&sender_id).unwrap().state.balance, 100);
    assert_eq!(ledger.get(&receiver_id).unwrap().state.balance, 0);
}

#[test]
fn ledger_delta_transfer_source_not_found() {
    let mut ledger = Ledger::new();
    let receiver = Cell::with_balance(test_key(2), test_token(2), 0);
    let receiver_id = receiver.id;
    ledger.insert_cell(receiver).unwrap();

    let fake_sender = CellId::derive_raw(&test_key(99), &test_token(99));
    let delta = LedgerDelta {
        created: Vec::new(),
        updated: Vec::new(),
        computron_transfers: vec![(fake_sender, receiver_id, 10)],
    };

    let err = ledger.apply_delta(&delta).unwrap_err();
    assert_eq!(err, LedgerError::TransferSourceNotFound(fake_sender));
}

#[test]
fn ledger_delta_transfer_dest_not_found() {
    let mut ledger = Ledger::new();
    let sender = Cell::with_balance(test_key(1), test_token(1), 100);
    let sender_id = sender.id;
    ledger.insert_cell(sender).unwrap();

    let fake_dest = CellId::derive_raw(&test_key(99), &test_token(99));
    let delta = LedgerDelta {
        created: Vec::new(),
        updated: Vec::new(),
        computron_transfers: vec![(sender_id, fake_dest, 10)],
    };

    let err = ledger.apply_delta(&delta).unwrap_err();
    assert_eq!(err, LedgerError::TransferDestNotFound(fake_dest));
}

#[test]
fn ledger_delta_permission_changes() {
    let mut ledger = Ledger::new();
    let id = ledger.create_cell(test_key(1), test_token(1));

    let new_perms = Permissions::zkapp();
    let delta = LedgerDelta {
        created: Vec::new(),
        updated: vec![(
            id,
            CellStateDelta {
                field_updates: Vec::new(),
                nonce_increment: false,
                balance_change: 0,
                permission_changes: Some(new_perms.clone()),
                capability_grants: Vec::new(),
                capability_revocations: Vec::new(),
            },
        )],
        computron_transfers: Vec::new(),
    };

    ledger.apply_delta(&delta).unwrap();
    assert_eq!(ledger.get(&id).unwrap().permissions, new_perms);
}

#[test]
fn ledger_delta_capability_grant_and_revoke() {
    let mut ledger = Ledger::new();
    let id = ledger.create_cell(test_key(1), test_token(1));
    let target = CellId::derive_raw(&test_key(2), &test_token(2));

    // Grant a capability.
    let cap_ref = CapabilityRef {
        target,
        slot: 0,
        permissions: AuthRequired::Signature,
        breadstuff: None,
        expires_at: None,
        allowed_effects: None,
    };
    let delta = LedgerDelta {
        created: Vec::new(),
        updated: vec![(
            id,
            CellStateDelta {
                field_updates: Vec::new(),
                nonce_increment: false,
                balance_change: 0,
                permission_changes: None,
                capability_grants: vec![cap_ref],
                capability_revocations: Vec::new(),
            },
        )],
        computron_transfers: Vec::new(),
    };

    ledger.apply_delta(&delta).unwrap();
    let cell = ledger.get(&id).unwrap();
    assert!(cell.capabilities.has_access(&target));

    // Revoke it.
    // The grant_with_breadstuff call assigns a new slot (0 in this case since it's the first).
    let granted_slot = cell.capabilities.iter().next().unwrap().slot;
    let delta2 = LedgerDelta {
        created: Vec::new(),
        updated: vec![(
            id,
            CellStateDelta {
                field_updates: Vec::new(),
                nonce_increment: false,
                balance_change: 0,
                permission_changes: None,
                capability_grants: Vec::new(),
                capability_revocations: vec![granted_slot],
            },
        )],
        computron_transfers: Vec::new(),
    };

    ledger.apply_delta(&delta2).unwrap();
    let cell = ledger.get(&id).unwrap();
    assert!(!cell.capabilities.has_access(&target));
}

#[test]
fn ledger_delta_complex_atomic_operation() {
    let mut ledger = Ledger::new();
    let alice = Cell::with_balance(test_key(1), test_token(1), 10000);
    let alice_id = alice.id;
    ledger.insert_cell(alice).unwrap();

    // Create Bob, update Alice, transfer from Alice to Bob — all in one delta.
    let bob = Cell::with_balance(test_key(2), test_token(2), 0);
    let bob_id = bob.id;

    let delta = LedgerDelta {
        created: vec![bob],
        updated: vec![(
            alice_id,
            CellStateDelta {
                field_updates: vec![(0, field_from_u64(42))],
                nonce_increment: true,
                balance_change: 0,
                permission_changes: None,
                capability_grants: Vec::new(),
                capability_revocations: Vec::new(),
            },
        )],
        computron_transfers: vec![(alice_id, bob_id, 500)],
    };

    ledger.apply_delta(&delta).unwrap();
    let alice_cell = ledger.get(&alice_id).unwrap();
    assert_eq!(alice_cell.state.balance, 9500);
    assert_eq!(alice_cell.state.nonce, 1);
    assert_eq!(alice_cell.state.fields[0], field_from_u64(42));

    let bob_cell = ledger.get(&bob_id).unwrap();
    assert_eq!(bob_cell.state.balance, 500);
}

// ============================================================
// Precondition tests
// ============================================================

fn default_eval_ctx() -> EvalContext {
    EvalContext {
        block_height: 100,
        timestamp: 1700000000,
        ..Default::default()
    }
}

#[test]
fn preconditions_empty_always_passes() {
    let pre = Preconditions::default();
    let state = CellState::new(1000);
    let ctx = default_eval_ctx();
    assert!(pre.evaluate(&state, &ctx).is_ok());
}

#[test]
fn preconditions_nonce_match() {
    let pre = Preconditions {
        cell_state: Some(CellStatePrecondition {
            nonce: Some(5),
            ..Default::default()
        }),
        ..Default::default()
    };
    let mut state = CellState::new(0);
    state.nonce = 5;
    assert!(pre.evaluate(&state, &default_eval_ctx()).is_ok());
}

#[test]
fn preconditions_nonce_mismatch() {
    let pre = Preconditions {
        cell_state: Some(CellStatePrecondition {
            nonce: Some(5),
            ..Default::default()
        }),
        ..Default::default()
    };
    let mut state = CellState::new(0);
    state.nonce = 3;
    let err = pre.evaluate(&state, &default_eval_ctx()).unwrap_err();
    assert_eq!(
        err,
        PreconditionError::NonceMismatch {
            expected: 5,
            actual: 3
        }
    );
}

#[test]
fn preconditions_min_balance_satisfied() {
    let pre = Preconditions {
        cell_state: Some(CellStatePrecondition {
            min_balance: Some(100),
            ..Default::default()
        }),
        ..Default::default()
    };
    let state = CellState::new(500);
    assert!(pre.evaluate(&state, &default_eval_ctx()).is_ok());
}

#[test]
fn preconditions_min_balance_insufficient() {
    let pre = Preconditions {
        cell_state: Some(CellStatePrecondition {
            min_balance: Some(1000),
            ..Default::default()
        }),
        ..Default::default()
    };
    let state = CellState::new(500);
    let err = pre.evaluate(&state, &default_eval_ctx()).unwrap_err();
    assert_eq!(
        err,
        PreconditionError::InsufficientBalance {
            required: 1000,
            actual: 500
        }
    );
}

#[test]
fn preconditions_field_equals_satisfied() {
    let pre = Preconditions {
        cell_state: Some(CellStatePrecondition {
            field_equals: vec![(2, field_from_u64(42))],
            ..Default::default()
        }),
        ..Default::default()
    };
    let mut state = CellState::new(0);
    state.fields[2] = field_from_u64(42);
    assert!(pre.evaluate(&state, &default_eval_ctx()).is_ok());
}

#[test]
fn preconditions_field_equals_mismatch() {
    let pre = Preconditions {
        cell_state: Some(CellStatePrecondition {
            field_equals: vec![(2, field_from_u64(42))],
            ..Default::default()
        }),
        ..Default::default()
    };
    let mut state = CellState::new(0);
    state.fields[2] = field_from_u64(99);
    let err = pre.evaluate(&state, &default_eval_ctx()).unwrap_err();
    assert_eq!(
        err,
        PreconditionError::FieldMismatch {
            index: 2,
            expected: field_from_u64(42),
            actual: field_from_u64(99),
        }
    );
}

#[test]
fn preconditions_field_invalid_index() {
    let pre = Preconditions {
        cell_state: Some(CellStatePrecondition {
            field_equals: vec![(99, field_from_u64(1))],
            ..Default::default()
        }),
        ..Default::default()
    };
    let state = CellState::new(0);
    let err = pre.evaluate(&state, &default_eval_ctx()).unwrap_err();
    assert_eq!(err, PreconditionError::InvalidFieldIndex { index: 99 });
}

#[test]
fn preconditions_network_min_height() {
    let pre = Preconditions {
        network: Some(NetworkPrecondition {
            min_height: Some(50),
            max_height: None,
        }),
        ..Default::default()
    };
    let state = CellState::new(0);

    // height=100 >= 50 → OK.
    assert!(pre.evaluate(&state, &default_eval_ctx()).is_ok());

    // height=30 < 50 → fail.
    let ctx = EvalContext {
        block_height: 30,
        timestamp: 0,
        ..Default::default()
    };
    let err = pre.evaluate(&state, &ctx).unwrap_err();
    assert_eq!(
        err,
        PreconditionError::HeightTooLow {
            required: 50,
            actual: 30
        }
    );
}

#[test]
fn preconditions_network_max_height() {
    let pre = Preconditions {
        network: Some(NetworkPrecondition {
            min_height: None,
            max_height: Some(50),
        }),
        ..Default::default()
    };
    let state = CellState::new(0);

    let ctx = EvalContext {
        block_height: 100,
        timestamp: 0,
        ..Default::default()
    };
    let err = pre.evaluate(&state, &ctx).unwrap_err();
    assert_eq!(
        err,
        PreconditionError::HeightTooHigh {
            max: 50,
            actual: 100
        }
    );
}

#[test]
fn preconditions_time_range_valid() {
    let pre = Preconditions {
        valid_while: Some(TimeRange::new(1699000000, 1701000000)),
        ..Default::default()
    };
    let state = CellState::new(0);
    let ctx = EvalContext {
        block_height: 100,
        timestamp: 1700000000,
        ..Default::default()
    };
    assert!(pre.evaluate(&state, &ctx).is_ok());
}

#[test]
fn preconditions_time_range_expired() {
    let pre = Preconditions {
        valid_while: Some(TimeRange::new(1699000000, 1699500000)),
        ..Default::default()
    };
    let state = CellState::new(0);
    let ctx = EvalContext {
        block_height: 100,
        timestamp: 1700000000,
        ..Default::default()
    };
    let err = pre.evaluate(&state, &ctx).unwrap_err();
    assert_eq!(
        err,
        PreconditionError::TimeOutOfRange {
            timestamp: 1700000000,
            start: 1699000000,
            end: 1699500000,
        }
    );
}

#[test]
fn preconditions_time_range_not_yet_valid() {
    let pre = Preconditions {
        valid_while: Some(TimeRange::new(1800000000, 1900000000)),
        ..Default::default()
    };
    let state = CellState::new(0);
    let ctx = EvalContext {
        block_height: 100,
        timestamp: 1700000000,
        ..Default::default()
    };
    let err = pre.evaluate(&state, &ctx).unwrap_err();
    matches!(err, PreconditionError::TimeOutOfRange { .. });
}

#[test]
fn preconditions_combined_all_pass() {
    let pre = Preconditions {
        cell_state: Some(CellStatePrecondition {
            nonce: Some(3),
            min_balance: Some(100),
            field_equals: vec![(0, field_from_u64(7))],
            ..Default::default()
        }),
        network: Some(NetworkPrecondition {
            min_height: Some(50),
            max_height: Some(200),
        }),
        valid_while: Some(TimeRange::new(1699000000, 1701000000)),
        witnessed: Vec::new(),
    };
    let mut state = CellState::new(500);
    state.nonce = 3;
    state.fields[0] = field_from_u64(7);
    let ctx = EvalContext {
        block_height: 100,
        timestamp: 1700000000,
        ..Default::default()
    };
    assert!(pre.evaluate(&state, &ctx).is_ok());
}

#[test]
fn preconditions_combined_first_failure_reported() {
    let pre = Preconditions {
        cell_state: Some(CellStatePrecondition {
            nonce: Some(3),
            min_balance: Some(100),
            ..Default::default()
        }),
        ..Default::default()
    };
    let mut state = CellState::new(500);
    state.nonce = 1; // nonce mismatch — should be reported first.
    let err = pre.evaluate(&state, &default_eval_ctx()).unwrap_err();
    assert_eq!(
        err,
        PreconditionError::NonceMismatch {
            expected: 3,
            actual: 1
        }
    );
}

#[test]
fn time_range_contains_boundaries() {
    let range = TimeRange::new(100, 200);
    assert!(range.contains(100)); // inclusive start
    assert!(range.contains(200)); // inclusive end
    assert!(range.contains(150));
    assert!(!range.contains(99));
    assert!(!range.contains(201));
}

// ============================================================
// Integration / scenario tests
// ============================================================

#[test]
fn scenario_agent_lifecycle() {
    let mut ledger = Ledger::new();

    // 1. Create a parent agent cell.
    let parent_pk = test_key(1);
    let default_token = [0u8; 32]; // default token domain
    let parent_id = ledger.create_cell(parent_pk, default_token);

    // Give parent some computrons.
    ledger.get_mut(&parent_id).unwrap().state.balance = 10000;

    // 2. Parent spawns a child agent.
    let child_pk = test_key(2);
    let child = {
        let parent = ledger.get(&parent_id).unwrap();
        parent.spawn_child(child_pk, default_token)
    };
    let child_id = child.id;
    ledger.insert_cell(child).unwrap();

    // 3. Parent grants capability to reach child.
    {
        let parent = ledger.get_mut(&parent_id).unwrap();
        parent.capabilities.grant(child_id, AuthRequired::Signature);
    }

    // 4. Transfer computrons from parent to child.
    let delta = LedgerDelta {
        created: Vec::new(),
        updated: Vec::new(),
        computron_transfers: vec![(parent_id, child_id, 2000)],
    };
    ledger.apply_delta(&delta).unwrap();

    // 5. Verify state.
    let parent = ledger.get(&parent_id).unwrap();
    assert_eq!(parent.state.balance, 8000);
    assert!(parent.capabilities.has_access(&child_id));

    let child = ledger.get(&child_id).unwrap();
    assert_eq!(child.state.balance, 2000);
    assert_eq!(child.delegate, Some(parent_id));

    // 6. Child CANNOT access parent (isolation).
    assert!(!child.capabilities.has_access(&parent_id));
}

#[test]
fn scenario_capability_delegation_chain() {
    let mut ledger = Ledger::new();
    let default_token = [0u8; 32];

    // Create A, B, C.
    let a_id = ledger.create_cell(test_key(1), default_token);
    let b_id = ledger.create_cell(test_key(2), default_token);
    let c_id = ledger.create_cell(test_key(3), default_token);

    // A can reach B.
    ledger
        .get_mut(&a_id)
        .unwrap()
        .capabilities
        .grant(b_id, AuthRequired::Either);

    // B can reach C.
    ledger
        .get_mut(&b_id)
        .unwrap()
        .capabilities
        .grant(c_id, AuthRequired::Signature);

    // A cannot directly reach C (capability isolation).
    let a = ledger.get(&a_id).unwrap();
    assert!(a.capabilities.has_access(&b_id));
    assert!(!a.capabilities.has_access(&c_id));

    // B can reach C but not A.
    let b = ledger.get(&b_id).unwrap();
    assert!(b.capabilities.has_access(&c_id));
    assert!(!b.capabilities.has_access(&a_id));

    // C has no capabilities.
    let c = ledger.get(&c_id).unwrap();
    assert!(c.capabilities.is_empty());
}

#[test]
fn scenario_permission_escalation_prevention() {
    // A cell with Signature permissions cannot be widened to None without auth.
    let perms = Permissions::default_user();

    // set_permissions itself requires Signature.
    assert!(perms.check(Action::SetPermissions, &AuthKind::Signature));
    assert!(!perms.check(Action::SetPermissions, &AuthKind::Proof));

    // A frozen cell cannot have its permissions changed.
    let frozen = Permissions::frozen();
    assert!(!frozen.check(Action::SetPermissions, &AuthKind::Signature));
    assert!(!frozen.check(Action::SetPermissions, &AuthKind::Proof));
}

#[test]
fn scenario_zkapp_cell_with_verification_key() {
    let mut ledger = Ledger::new();

    // Create a zkApp cell.
    let cell = Cell::new(test_key(1), test_token(1));
    let id = cell.id;
    ledger.insert_cell(cell).unwrap();

    // Set verification key and switch to proof permissions.
    let vk_data = vec![0xDE, 0xAD, 0xBE, 0xEF, 0x01, 0x02, 0x03];
    let vk = VerificationKey::new(vk_data.clone());
    let expected_hash = *blake3::hash(&vk_data).as_bytes();

    {
        let cell = ledger.get_mut(&id).unwrap();
        cell.verification_key = Some(vk);
        cell.permissions = Permissions::zkapp();
    }

    let cell = ledger.get(&id).unwrap();
    assert_eq!(cell.verification_key.as_ref().unwrap().hash, expected_hash);
    assert_eq!(cell.permissions.send, AuthRequired::Proof);

    // Only proofs can send now.
    assert!(cell.permissions.check(Action::Send, &AuthKind::Proof));
    assert!(!cell.permissions.check(Action::Send, &AuthKind::Signature));
}

#[test]
fn scenario_merkle_proof_after_mutations() {
    let mut ledger = Ledger::new();

    // Create several cells.
    let ids: Vec<CellId> = (0..5)
        .map(|i| ledger.create_cell(test_key(i), test_token(i)))
        .collect();

    // Mutate one.
    ledger.get_mut(&ids[2]).unwrap().state.balance = 999;
    // Manually recompute root (since get_mut doesn't trigger it).
    // We need to use apply_delta or direct operations.

    // Use a delta to properly update.
    let delta = LedgerDelta {
        created: Vec::new(),
        updated: vec![(
            ids[2],
            CellStateDelta {
                field_updates: vec![(0, field_from_u64(77))],
                nonce_increment: true,
                balance_change: 1000,
                permission_changes: None,
                capability_grants: Vec::new(),
                capability_revocations: Vec::new(),
            },
        )],
        computron_transfers: Vec::new(),
    };
    ledger.apply_delta(&delta).unwrap();

    // All proofs should still be valid.
    for id in &ids {
        let proof = ledger.membership_proof(id).unwrap();
        assert!(proof.verify(), "proof invalid for {id} after mutation");
    }
}

#[test]
fn scenario_atomic_failure_no_partial_apply() {
    let mut ledger = Ledger::new();
    let sender = Cell::with_balance(test_key(1), test_token(1), 100);
    let sender_id = sender.id;
    ledger.insert_cell(sender).unwrap();

    // This delta creates a cell and then tries to transfer MORE than sender has.
    let new_cell = Cell::with_balance(test_key(2), test_token(2), 0);
    let new_id = new_cell.id;

    let delta = LedgerDelta {
        created: vec![new_cell],
        updated: Vec::new(),
        computron_transfers: vec![(sender_id, new_id, 9999)], // way too much
    };

    let err = ledger.apply_delta(&delta);
    assert!(err.is_err());

    // The new cell should NOT have been created (atomic failure).
    // Note: our current implementation validates before applying, so this holds.
    assert!(!ledger.contains(&new_id));
    assert_eq!(ledger.get(&sender_id).unwrap().state.balance, 100);
}

#[test]
fn scenario_multiple_grants_same_target() {
    let mut caps = CapabilitySet::new();
    let target = CellId::derive_raw(&test_key(1), &test_token(1));

    // Grant multiple capabilities to the same target with different perms.
    let s1 = caps.grant(target, AuthRequired::None).unwrap();
    let s2 = caps.grant(target, AuthRequired::Signature).unwrap();
    let s3 = caps.grant(target, AuthRequired::Proof).unwrap();

    assert_eq!(caps.len(), 3);
    assert_ne!(s1, s2);
    assert_ne!(s2, s3);

    // Revoking one doesn't revoke others.
    caps.revoke(s1);
    assert!(caps.has_access(&target)); // still accessible via s2, s3
    assert_eq!(caps.len(), 2);

    caps.revoke(s2);
    assert!(caps.has_access(&target)); // still via s3
    assert_eq!(caps.len(), 1);

    caps.revoke(s3);
    assert!(!caps.has_access(&target)); // now gone
    assert_eq!(caps.len(), 0);
}

#[test]
fn scenario_ledger_iter() {
    let mut ledger = Ledger::new();
    let id1 = ledger.create_cell(test_key(1), test_token(1));
    let id2 = ledger.create_cell(test_key(2), test_token(2));

    let all_ids: Vec<CellId> = ledger.iter().map(|(id, _)| *id).collect();
    assert_eq!(all_ids.len(), 2);
    assert!(all_ids.contains(&id1));
    assert!(all_ids.contains(&id2));
}

#[test]
fn cell_state_delta_empty_is_noop() {
    let mut ledger = Ledger::new();
    let cell = Cell::with_balance(test_key(1), test_token(1), 500);
    let id = cell.id;
    ledger.insert_cell(cell).unwrap();

    let root_before = ledger.root();

    let delta = LedgerDelta {
        created: Vec::new(),
        updated: vec![(id, CellStateDelta::empty())],
        computron_transfers: Vec::new(),
    };

    ledger.apply_delta(&delta).unwrap();

    // State unchanged.
    let cell = ledger.get(&id).unwrap();
    assert_eq!(cell.state.balance, 500);
    assert_eq!(cell.state.nonce, 0);

    // Root may change due to recomputation (but state hash is same) — actually
    // the hash depends on state which hasn't changed, so root should be same.
    assert_eq!(ledger.root(), root_before);
}

#[test]
fn ledger_incremental_root_matches_full_rebuild() {
    let mut ledger = Ledger::new();

    // Create several cells.
    let ids: Vec<CellId> = (0..10)
        .map(|i| ledger.create_cell(test_key(i), test_token(i)))
        .collect();

    // Verify incremental matches full rebuild after creation.
    assert_eq!(ledger.root(), ledger.recompute_root_standalone());

    // Apply an update delta (incremental path).
    let delta = LedgerDelta {
        created: Vec::new(),
        updated: vec![
            (
                ids[3],
                CellStateDelta {
                    field_updates: vec![(0, field_from_u64(100))],
                    nonce_increment: true,
                    balance_change: 500,
                    permission_changes: None,
                    capability_grants: Vec::new(),
                    capability_revocations: Vec::new(),
                },
            ),
            (
                ids[7],
                CellStateDelta {
                    field_updates: vec![(2, field_from_u64(999))],
                    nonce_increment: false,
                    balance_change: 1000,
                    permission_changes: None,
                    capability_grants: Vec::new(),
                    capability_revocations: Vec::new(),
                },
            ),
        ],
        computron_transfers: Vec::new(),
    };

    ledger.apply_delta(&delta).unwrap();

    // The incremental root must match a full from-scratch computation.
    assert_eq!(ledger.root(), ledger.recompute_root_standalone());

    // Apply a transfer (also incremental).
    let cell_a = Cell::with_balance(test_key(20), test_token(20), 5000);
    let cell_b = Cell::with_balance(test_key(21), test_token(21), 100);
    let a_id = cell_a.id;
    let b_id = cell_b.id;

    let delta2 = LedgerDelta {
        created: vec![cell_a, cell_b],
        updated: Vec::new(),
        computron_transfers: Vec::new(),
    };
    ledger.apply_delta(&delta2).unwrap();
    assert_eq!(ledger.root(), ledger.recompute_root_standalone());

    // Now do a transfer (incremental update, no new cells).
    let delta3 = LedgerDelta {
        created: Vec::new(),
        updated: Vec::new(),
        computron_transfers: vec![(a_id, b_id, 2000)],
    };
    ledger.apply_delta(&delta3).unwrap();
    assert_eq!(ledger.root(), ledger.recompute_root_standalone());
}

// ============================================================
// Field visibility / progressive disclosure tests
// ============================================================

use crate::state::{FieldVisibility, PublicFieldView};

#[test]
fn test_committed_field_not_visible() {
    // A committed field returns its hash, not the actual value.
    let mut state = CellState::new(0);
    let secret_value = field_from_u64(12345);
    state.set_field(0, secret_value);
    state.set_field_visibility(0, FieldVisibility::Committed, 42);

    // The public view should be a commitment hash, not the value.
    let view = state.get_field_public(0).unwrap();
    match view {
        PublicFieldView::Committed(hash) => {
            // The hash should NOT equal the raw value.
            assert_ne!(hash, secret_value);
            // The hash should be deterministic.
            let expected = {
                let mut hasher = blake3::Hasher::new();
                hasher.update(&secret_value);
                hasher.update(&42u64.to_le_bytes());
                *hasher.finalize().as_bytes()
            };
            assert_eq!(hash, expected);
        }
        PublicFieldView::Revealed(_) => {
            panic!("expected Committed view, got Revealed");
        }
    }

    // A public field returns the actual value.
    state.set_field(1, field_from_u64(99));
    let view = state.get_field_public(1).unwrap();
    assert_eq!(view, PublicFieldView::Revealed(field_from_u64(99)));
}

#[test]
fn test_selectively_disclosable_field() {
    let mut state = CellState::new(0);
    let value = field_from_u64(777);
    state.set_field(3, value);
    state.set_field_visibility(3, FieldVisibility::SelectivelyDisclosable, 100);

    // Also returns committed view.
    let view = state.get_field_public(3).unwrap();
    assert!(matches!(view, PublicFieldView::Committed(_)));

    // The underlying value is still accessible internally.
    assert_eq!(state.fields[3], value);
}

#[test]
fn test_visibility_default_is_public() {
    let state = CellState::new(0);
    for i in 0..STATE_SLOTS {
        assert_eq!(state.field_visibility[i], FieldVisibility::Public);
        assert_eq!(state.commitments[i], None);
    }
}

#[test]
fn test_visibility_transition_to_public_clears_commitment() {
    let mut state = CellState::new(0);
    state.set_field(0, field_from_u64(42));
    state.set_field_visibility(0, FieldVisibility::Committed, 1);
    assert!(state.commitments[0].is_some());

    // Transition back to public.
    state.set_field_visibility(0, FieldVisibility::Public, 0);
    assert!(state.commitments[0].is_none());
    assert_eq!(
        state.get_field_public(0).unwrap(),
        PublicFieldView::Revealed(field_from_u64(42))
    );
}

// ============================================================
// Audit AUDIT-cell.md — adversarial tests (P0-1, P1-2, P1-5,
// P1-6, P2-1, P2-2, P2-3)
// ============================================================

use crate::facet::{EFFECT_TRANSFER, FACET_TRANSFER_ONLY, is_effect_permitted};

/// P0-1 adversarial: sealed `Cell` identity fields cannot be mutated
/// from outside the cell crate.
///
/// Inside the crate (this test module) the `pub(crate)` fields ARE
/// accessible — that's the point. The compile-fail check that external
/// code cannot mutate them lives in
/// `cell/tests/compile_fail_sealing.rs` and is exercised via the
/// trybuild harness as a separate file.
///
/// Here we verify the **accessor** surface that external code is
/// expected to use is read-only.
#[test]
fn p0_1_cell_accessors_are_read_only() {
    let cell = Cell::new(test_key(1), test_token(1));

    // Read accessors return values, not mutable references.
    let _id: CellId = cell.id();
    let _pk: &[u8; 32] = cell.public_key();
    let _tok: &[u8; 32] = cell.token_id();

    // No `set_id`/`set_public_key`/`set_token_id` method exists; identity
    // is content-addressed and immutable after construction.
}

/// P0-1 adversarial: sealed `CellState` numeric fields are read-only
/// from outside; mutations must go through the explicit mutator API.
#[test]
fn p0_1_cell_state_accessors_are_read_only() {
    let state = CellState::new(100);
    let _bal: u64 = state.balance();
    let _nonce: u64 = state.nonce();
    let _ps: bool = state.proved_state();
    let _de: u64 = state.delegation_epoch();
}

/// P1-2 adversarial: writing a field via `set_field` no longer leaks
/// the plaintext through `get_field_public`. Previously, if the
/// visibility was `Committed`/`SelectivelyDisclosable` but the stored
/// commitment had been invalidated by `set_field`, the function
/// returned `PublicFieldView::Revealed(plaintext)`. Now it returns the
/// non-informative zero-hash sentinel.
#[test]
fn p1_2_set_field_does_not_leak_committed_plaintext() {
    let mut state = CellState::new(0);
    let secret = field_from_u64(0xDEADBEEF);
    state.set_field(3, secret);
    state.set_field_visibility(3, FieldVisibility::Committed, 42);
    // A holder later overwrites the field — the stale commitment is
    // invalidated.
    let new_secret = field_from_u64(0xCAFEBABE);
    state.set_field(3, new_secret);

    // The public view MUST NOT reveal `new_secret`.
    let view = state.get_field_public(3).expect("index in range");
    match view {
        PublicFieldView::Revealed(_) => {
            panic!("P1-2 regression: committed-field plaintext leaked after set_field")
        }
        PublicFieldView::Committed(hash) => {
            // Sentinel: all-zero hash signals "stale commitment, ask the
            // holder to re-commit." Non-informative.
            assert_eq!(hash, [0u8; 32]);
        }
    }
}

/// P1-5 adversarial: `Cell::spawn_child_with_delegation` is not
/// callable from outside the cell crate (now `pub(crate)`).
///
/// Compile-time enforcement is the real win; here we just verify the
/// in-crate path still works, since the executor needs to be able to
/// reach it from the cell crate's downstream callers via a controlled
/// adapter.
#[test]
fn p1_5_spawn_child_with_delegation_in_crate() {
    let parent = Cell::new(test_key(1), test_token(1));
    let child = parent.spawn_child_with_delegation(test_key(2), test_token(2), 1, 100, 1000);
    let delegation = child.delegation.expect("delegation present");
    // The placeholder signature is all-zero — the audit's point is that
    // such delegations must always run signature verification. Now that
    // the function is `pub(crate)`, only the cell crate (and downstream
    // re-exports it deliberately exposes) can produce them.
    assert_eq!(delegation.parent_signature, [0u8; 64]);
}

/// P1-6 adversarial: `Ledger::update_with` rejects mutations that
/// break the content-address invariant `id == derive_raw(pk, tok)`.
///
/// Without this guard, a closure could rewrite `public_key` while
/// leaving `id` unchanged, leaving the cell at a HashMap key
/// inconsistent with its content.
#[test]
fn p1_6_update_with_rejects_pubkey_drift() {
    let mut ledger = Ledger::new();
    let id = ledger.create_cell(test_key(1), test_token(1));

    // Honest mutation: change a permission. Integrity preserved.
    let ok = ledger.update_with(&id, |cell| {
        cell.permissions = Permissions::default();
    });
    assert!(ok.is_ok());

    // Adversarial mutation: rewrite the inner public_key field to point
    // at a different key (via the `pub(crate)` access this test has).
    // This breaks the content-address invariant and update_with must
    // reject and restore.
    let adversarial = ledger.update_with(&id, |cell| {
        cell.public_key = test_key(99);
    });
    assert!(matches!(adversarial, Err(LedgerError::InvalidDelta(_))));

    // The cell must have been restored to its pre-mutation state.
    let restored = ledger.get(&id).expect("cell present");
    assert_eq!(*restored.public_key(), test_key(1));
    assert!(restored.verify_id_integrity());
}

/// P2-1 adversarial: `is_effect_permitted(Some(0), _)` now denies.
/// Previously, `Some(0)` was a backward-compat alias for "unrestricted"
/// — an attacker who got a faceted capability with `allowed_effects:
/// Some(0)` had unrestricted access while appearing heavily faceted.
#[test]
fn p2_1_zero_mask_denies_all() {
    // No mask = unrestricted.
    assert!(is_effect_permitted(None, EFFECT_TRANSFER));
    // Zero mask = deny all (new semantics).
    assert!(!is_effect_permitted(Some(0), EFFECT_TRANSFER));
    // Specific mask still works.
    assert!(is_effect_permitted(
        Some(FACET_TRANSFER_ONLY),
        EFFECT_TRANSFER
    ));
}

/// P2-2 adversarial: `increment_nonce` returns `false` at u64::MAX
/// rather than wrapping. This prevents replay of historical actions
/// after 2^64 increments.
#[test]
fn p2_2_increment_nonce_overflow_rejected() {
    let mut state = CellState::new(0);
    // Force the boundary condition via the pub(crate) field (in-crate).
    state.nonce = u64::MAX;
    assert!(!state.increment_nonce());
    // Nonce must NOT have wrapped to zero.
    assert_eq!(state.nonce(), u64::MAX);
}

/// P2-2 adversarial: `bump_delegation_epoch` also refuses to wrap.
#[test]
fn p2_2_bump_delegation_epoch_overflow_rejected() {
    let mut state = CellState::new(0);
    state.delegation_epoch = u64::MAX;
    assert!(!state.bump_delegation_epoch());
    assert_eq!(state.delegation_epoch(), u64::MAX);
}

/// P2-2 adversarial: ledger `apply_delta` returns `InvalidDelta` on
/// nonce overflow rather than silently wrapping.
#[test]
fn p2_2_apply_delta_rejects_nonce_overflow() {
    let mut ledger = Ledger::new();
    let id = ledger.create_cell(test_key(1), test_token(1));
    // Set nonce to the boundary in-crate.
    ledger
        .update_with(&id, |c| {
            c.state.nonce = u64::MAX;
        })
        .unwrap();

    let delta = LedgerDelta {
        created: Vec::new(),
        updated: vec![(
            id,
            CellStateDelta {
                field_updates: Vec::new(),
                nonce_increment: true,
                balance_change: 0,
                permission_changes: None,
                capability_grants: Vec::new(),
                capability_revocations: Vec::new(),
            },
        )],
        computron_transfers: Vec::new(),
    };

    let result = ledger.apply_delta(&delta);
    assert!(matches!(result, Err(LedgerError::InvalidDelta(_))));
    // Nonce must not have wrapped.
    assert_eq!(ledger.get(&id).unwrap().state.nonce(), u64::MAX);
}

/// P2-3 adversarial: a freshly-constructed cell satisfies
/// `verify_id_integrity`, and breaking the invariant (only possible
/// in-crate now) is detectable.
#[test]
fn p2_3_verify_id_integrity_catches_drift() {
    let mut cell = Cell::new(test_key(1), test_token(1));
    assert!(cell.verify_id_integrity());

    // Drift the public_key in-crate (this is what external code can no
    // longer do; we simulate the attack from inside).
    cell.public_key = test_key(99);
    assert!(
        !cell.verify_id_integrity(),
        "verify_id_integrity must detect public_key drift"
    );
}

/// P0-2 cross-binding: the three commitment derivations all agree
/// byte-for-byte after the canonical-commitment refactor.
#[test]
fn p0_2_three_commitments_agree() {
    let cell = Cell::new(test_key(7), test_token(11));
    let canonical = crate::commitment::compute_canonical_state_commitment(&cell);
    let from_cell = cell.state_commitment();
    let from_ledger = Ledger::hash_cell_canonical(&cell);
    assert_eq!(canonical, from_cell);
    assert_eq!(canonical, from_ledger);
}

/// P0-2 adversarial: changing `permissions` propagates into all three
/// commitments (previously a circuit-side gap).
#[test]
fn p0_2_permission_change_propagates_to_state_commitment() {
    let mut cell = Cell::new(test_key(7), test_token(11));
    let before = cell.state_commitment();
    cell.permissions = Permissions::zkapp();
    let after = cell.state_commitment();
    assert_ne!(before, after);
}
