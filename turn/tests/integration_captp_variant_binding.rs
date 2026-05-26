//! Integration tests for the block1-bind closures of the CapTP runtime
//! variants (BLOCK1-BIND-CLOSURE-NOTES.md sites 1, 2, 3). Each test
//! constructs a Turn carrying the extended variant and verifies that
//!
//! - the honest path executes and commits;
//! - a forged variant value (permissions wider than the cell's tier;
//!   expected_permissions disagreeing with the swiss-table entry) is
//!   rejected by the apply gate.
//!
//! The AIR-side binding (PARAMs projected from the runtime variant) is
//! exercised by `tests/src/every_variant_roundtrip.rs`; this suite
//! pins the runtime-side soundness gate.

use pyana_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use pyana_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnExecutor,
    turn::Turn,
};

fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn make_cell(seed: u8, balance: u64, perms: Permissions) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = perms;
    cell
}

fn single_effect_turn(agent: CellId, target: CellId, nonce: u64, effect: Effect) -> Turn {
    let mut forest = CallForest::new();
    let action = Action {
        target,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![effect],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    };
    forest.add_root(action);
    Turn {
        agent,
        nonce,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

// ============================================================================
// SITE 2: ExportSturdyRef.permissions — runtime-variant extension
// ============================================================================

/// Honest path: a cell with `access: None` exports a sturdy ref with
/// `permissions: None`. Apply succeeds; the swiss-table entry the
/// federation mirror later materialises holds the same `None` tier the
/// AIR PI projects.
#[test]
fn export_sturdy_ref_honest_path_accepted() {
    let actor = make_cell(1, 1000, open_permissions());
    let target = make_cell(2, 0, open_permissions());
    let actor_id = actor.id();
    let target_id = target.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(actor).unwrap();
    ledger.insert_cell(target).unwrap();

    let effect = Effect::ExportSturdyRef {
        swiss_number: [0x42u8; 32],
        target: target_id,
        permissions: AuthRequired::None,
    };
    let turn = single_effect_turn(actor_id, target_id, 0, effect);

    let executor = TurnExecutor::new(ComputronCosts::zero());
    match executor.execute(&turn, &mut ledger) {
        pyana_turn::TurnResult::Committed { .. } => { /* expected */ }
        other => panic!(
            "honest ExportSturdyRef must commit, got {:?}",
            short(&other)
        ),
    }
}

/// Adversarial: a cell whose `access` requires `Signature` exports a
/// sturdy ref claiming `permissions: None`. The apply site rejects —
/// without this gate, a forged permissions value would let the AIR
/// PI attest authority the cell does not hold.
#[test]
fn export_sturdy_ref_rejects_wider_than_cell_access() {
    let actor = make_cell(1, 1000, open_permissions());
    // Target's access tier requires Signature; declaring None on the
    // export would widen authority. Open everything else to ensure
    // the rejection is on the permissions-narrowing check, not on a
    // cross-cell access guard.
    let mut sig_access = open_permissions();
    sig_access.access = AuthRequired::Signature;
    let target = make_cell(2, 0, sig_access);
    let actor_id = actor.id();
    let target_id = target.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(actor).unwrap();
    ledger.insert_cell(target).unwrap();

    let effect = Effect::ExportSturdyRef {
        swiss_number: [0x42u8; 32],
        target: target_id,
        permissions: AuthRequired::None, // wider than Signature
    };
    let turn = single_effect_turn(actor_id, target_id, 0, effect);

    let executor = TurnExecutor::new(ComputronCosts::zero());
    match executor.execute(&turn, &mut ledger) {
        pyana_turn::TurnResult::Rejected { reason, .. } => {
            let s = format!("{reason:?}");
            assert!(
                s.contains("ExportSturdyRef") && s.contains("narrower"),
                "expected ExportSturdyRef narrower-or-equal failure, got: {s}"
            );
        }
        other => panic!(
            "expected Rejected for wider permissions, got {:?}",
            short(&other)
        ),
    }
}

/// Adversarial: a Custom auth tier in the cell, mismatched Custom in
/// the variant. `Custom` vs anything-other-than-itself is incomparable
/// → narrower_or_equal is false → reject.
#[test]
fn export_sturdy_ref_rejects_custom_tier_mismatch() {
    let actor = make_cell(1, 1000, open_permissions());
    let mut custom_access = open_permissions();
    custom_access.access = AuthRequired::Custom {
        vk_hash: [0xAAu8; 32],
    };
    let target = make_cell(2, 0, custom_access);
    let actor_id = actor.id();
    let target_id = target.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(actor).unwrap();
    ledger.insert_cell(target).unwrap();

    // Declare a *different* Custom vk_hash → incomparable.
    let effect = Effect::ExportSturdyRef {
        swiss_number: [0x42u8; 32],
        target: target_id,
        permissions: AuthRequired::Custom {
            vk_hash: [0xBBu8; 32],
        },
    };
    let turn = single_effect_turn(actor_id, target_id, 0, effect);

    let executor = TurnExecutor::new(ComputronCosts::zero());
    match executor.execute(&turn, &mut ledger) {
        pyana_turn::TurnResult::Rejected { reason, .. } => {
            let s = format!("{reason:?}");
            assert!(
                s.contains("ExportSturdyRef") && s.contains("narrower"),
                "expected Custom-mismatch rejection, got: {s}"
            );
        }
        other => panic!(
            "expected Rejected for incomparable Custom tier, got {:?}",
            short(&other)
        ),
    }
}

/// Soundness: two ExportSturdyRef effects identical in every field
/// except `permissions` produce DIFFERENT effects_hashes. This is the
/// AIR-PI-binding witness — a forged permissions value cannot be
/// substituted by a malicious prover without invalidating the
/// receipt's effects commitment.
#[test]
fn export_sturdy_ref_permissions_distinct_effects_hash() {
    let target_id = CellId([0x11u8; 32]);
    let a = Effect::ExportSturdyRef {
        swiss_number: [0xCDu8; 32],
        target: target_id,
        permissions: AuthRequired::Signature,
    };
    let b = Effect::ExportSturdyRef {
        swiss_number: [0xCDu8; 32],
        target: target_id,
        permissions: AuthRequired::Proof,
    };
    assert_ne!(
        a.hash(),
        b.hash(),
        "ExportSturdyRef effects_hash must distinguish permissions tier"
    );
}

// ============================================================================
// SITE 1: EnlivenRef.expected_permissions — runtime-variant extension +
// bearer-c-list cross-check.
// ============================================================================

/// Honest path: the bearer's c-list grants a capability for
/// `expected_cell_id` with tier covering `expected_permissions`. Apply
/// succeeds.
#[test]
fn enliven_ref_honest_path_accepted() {
    let target = make_cell(2, 0, open_permissions());
    let target_id = target.id();
    // Bearer holds a c-list entry for `target_id` with tier=None.
    let mut bearer = make_cell(3, 0, open_permissions());
    bearer
        .capabilities
        .grant(target_id, AuthRequired::None)
        .unwrap();
    let bearer_id = bearer.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(target).unwrap();
    ledger.insert_cell(bearer).unwrap();

    let effect = Effect::EnlivenRef {
        swiss_number: [0x99u8; 32],
        bearer: bearer_id,
        expected_cell_id: target_id,
        expected_permissions: AuthRequired::None,
    };
    let turn = single_effect_turn(bearer_id, bearer_id, 0, effect);

    let executor = TurnExecutor::new(ComputronCosts::zero());
    match executor.execute(&turn, &mut ledger) {
        pyana_turn::TurnResult::Committed { .. } => { /* expected */ }
        other => panic!(
            "honest EnlivenRef must commit, got {:?}",
            short(&other)
        ),
    }
}

/// Adversarial: the bearer holds no capability for `expected_cell_id`.
/// The c-list lookup fails → apply gate rejects. Without this check,
/// the AIR's `expected_cell_id` PARAM (and the leaf bound into the
/// swiss_table_root chain) would attest a capability the bearer never
/// held.
#[test]
fn enliven_ref_rejects_no_capability_for_expected_cell() {
    let target = make_cell(2, 0, open_permissions());
    let target_id = target.id();
    let other_cell_id = CellId([0xEEu8; 32]); // bearer has NO cap for this
    let bearer = make_cell(3, 0, open_permissions());
    let bearer_id = bearer.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(target).unwrap();
    ledger.insert_cell(bearer).unwrap();

    let effect = Effect::EnlivenRef {
        swiss_number: [0x99u8; 32],
        bearer: bearer_id,
        expected_cell_id: other_cell_id, // forged: not in bearer's c-list
        expected_permissions: AuthRequired::None,
    };
    let turn = single_effect_turn(bearer_id, bearer_id, 0, effect);

    let executor = TurnExecutor::new(ComputronCosts::zero());
    match executor.execute(&turn, &mut ledger) {
        pyana_turn::TurnResult::Rejected { reason, .. } => {
            let s = format!("{reason:?}");
            assert!(
                s.contains("EnlivenRef") && s.contains("no"),
                "expected no-capability rejection, got: {s}"
            );
        }
        other => panic!(
            "expected Rejected for forged expected_cell_id, got {:?}",
            short(&other)
        ),
    }
}

/// Adversarial: bearer holds the c-list entry but only at tier
/// `Signature`; the variant declares `expected_permissions: None`
/// (wider than the held authority). The narrower-or-equal check
/// fails — the bearer cannot enliven authority broader than it
/// actually holds.
#[test]
fn enliven_ref_rejects_wider_than_held_capability() {
    let target = make_cell(2, 0, open_permissions());
    let target_id = target.id();
    let mut bearer = make_cell(3, 0, open_permissions());
    // Bearer's cap requires Signature → declaring None is widening.
    bearer
        .capabilities
        .grant(target_id, AuthRequired::Signature)
        .unwrap();
    let bearer_id = bearer.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(target).unwrap();
    ledger.insert_cell(bearer).unwrap();

    let effect = Effect::EnlivenRef {
        swiss_number: [0x99u8; 32],
        bearer: bearer_id,
        expected_cell_id: target_id,
        expected_permissions: AuthRequired::None, // widening
    };
    let turn = single_effect_turn(bearer_id, bearer_id, 0, effect);

    let executor = TurnExecutor::new(ComputronCosts::zero());
    match executor.execute(&turn, &mut ledger) {
        pyana_turn::TurnResult::Rejected { reason, .. } => {
            let s = format!("{reason:?}");
            assert!(
                s.contains("EnlivenRef") && s.contains("tier"),
                "expected widening rejection, got: {s}"
            );
        }
        other => panic!(
            "expected Rejected for wider expected_permissions, got {:?}",
            short(&other)
        ),
    }
}

/// Soundness: two EnlivenRef effects identical except for
/// `expected_permissions` produce distinct effects_hashes — a forged
/// permissions value cannot be substituted without invalidating the
/// receipt commitment that the verifier checks.
#[test]
fn enliven_ref_permissions_distinct_effects_hash() {
    let bearer = CellId([0x77u8; 32]);
    let target = CellId([0x88u8; 32]);
    let a = Effect::EnlivenRef {
        swiss_number: [0xCDu8; 32],
        bearer,
        expected_cell_id: target,
        expected_permissions: AuthRequired::Signature,
    };
    let b = Effect::EnlivenRef {
        swiss_number: [0xCDu8; 32],
        bearer,
        expected_cell_id: target,
        expected_permissions: AuthRequired::Proof,
    };
    assert_ne!(
        a.hash(),
        b.hash(),
        "EnlivenRef effects_hash must distinguish expected_permissions tier"
    );
}

/// Soundness complement: two EnlivenRef effects identical except for
/// `expected_cell_id` produce distinct effects_hashes.
#[test]
fn enliven_ref_expected_cell_id_distinct_effects_hash() {
    let bearer = CellId([0x77u8; 32]);
    let a = Effect::EnlivenRef {
        swiss_number: [0xCDu8; 32],
        bearer,
        expected_cell_id: CellId([0x11u8; 32]),
        expected_permissions: AuthRequired::None,
    };
    let b = Effect::EnlivenRef {
        swiss_number: [0xCDu8; 32],
        bearer,
        expected_cell_id: CellId([0x22u8; 32]),
        expected_permissions: AuthRequired::None,
    };
    assert_ne!(
        a.hash(),
        b.hash(),
        "EnlivenRef effects_hash must distinguish expected_cell_id"
    );
}

fn short(r: &pyana_turn::TurnResult) -> String {
    match r {
        pyana_turn::TurnResult::Committed { .. } => "Committed".into(),
        pyana_turn::TurnResult::Rejected { reason, .. } => format!("Rejected({reason:?})"),
    }
}
