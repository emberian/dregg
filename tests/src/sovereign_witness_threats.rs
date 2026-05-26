//! Sovereign-witness tests — Phase 1 algebraic teeth + wire-malleability.
//!
//! Layer: AIR (Effect VM) + canonical signing message + verifier-side
//! replay. See `AUDIT-sovereign-witness-teeth.md`,
//! `SOVEREIGN-WITNESS-AIR-DESIGN.md`, and `EXECUTOR-HONESTY-AUDIT.md` T9.
//!
//! Three concerns:
//!
//!   1. Phase 1: legal witness accepted; tampered key / sequence-regression
//!      rejected.
//!   2. T9 (executor skips sovereign witness): AIR must algebraically
//!      constrain the witness; it can't just decorate the receipt.
//!   3. Wire-malleability: turn v3 signing message must cover sovereign
//!      witnesses so tamper-then-sign fails.
//!
//! AIR-transition tests remain `#[ignore]`d on the sovereign-witness teeth
//! lane. Executor and wire-hash checks below are live when the implementation
//! already exposes the defense.

use std::collections::HashMap;

use dregg_cell::{
    AuthRequired, Cell, CellId, CellProgram, Ledger, Permissions, StateConstraint, field_from_u64,
};
use dregg_turn::action::{WitnessBlob, symbol};
use dregg_turn::{
    Action, ActionBuilder, Authorization, CallForest, ComputronCosts, DelegationMode, Effect,
    SovereignCellWitness, Turn, TurnBuilder, TurnError, TurnExecutor, TurnResult,
};
use dregg_types::{SigningKey, sign};

fn permissive_cell(seed: u8, balance: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(31);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    cell
}

fn signing_cell(seed: u8, balance: u64) -> (Cell, SigningKey) {
    let seed_bytes = [seed; 32];
    let signing_key = SigningKey::from_bytes(&seed_bytes);
    let mut cell = Cell::with_balance(*signing_key.public_key().as_bytes(), [0u8; 32], balance);
    cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    (cell, signing_key)
}

fn turn_with_witnesses(agent: CellId, witnesses: HashMap<CellId, SovereignCellWitness>) -> Turn {
    Turn {
        agent,
        nonce: 0,
        call_forest: dregg_turn::CallForest::new(),
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: witnesses,
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

fn set_field_turn(
    agent: CellId,
    target: CellId,
    witnesses: HashMap<CellId, SovereignCellWitness>,
) -> Turn {
    set_field_turn_with_action_witnesses(agent, target, witnesses, 0, [1u8; 32], vec![])
}

fn set_field_turn_with_action_witnesses(
    agent: CellId,
    target: CellId,
    witnesses: HashMap<CellId, SovereignCellWitness>,
    index: usize,
    value: [u8; 32],
    witness_blobs: Vec<WitnessBlob>,
) -> Turn {
    let mut call_forest = CallForest::new();
    call_forest.add_root(Action {
        target,
        method: symbol("set_field"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::SetField {
            cell: target,
            index,
            value,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs,
    });

    Turn {
        agent,
        nonce: 0,
        call_forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: witnesses,
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

fn two_set_field_turn(
    agent: CellId,
    first: CellId,
    second: CellId,
    witnesses: HashMap<CellId, SovereignCellWitness>,
) -> Turn {
    let first_action = ActionBuilder::new_unchecked_for_tests(first, "set_field", agent)
        .effect_set_field(first, 0, [1u8; 32])
        .build();
    let second_action = ActionBuilder::new_unchecked_for_tests(second, "set_field", agent)
        .effect_set_field(second, 0, [2u8; 32])
        .build();
    let mut builder = TurnBuilder::new(agent, 0);
    builder.add_action(first_action);
    builder.add_action(second_action);
    let mut turn = builder.fee(0).build();
    turn.sovereign_witnesses = witnesses;
    turn
}

fn dummy_sovereign_witness(
    cell: Cell,
    effects_hash: [u8; 32],
    sequence: u64,
) -> SovereignCellWitness {
    let cell_id = cell.id();
    SovereignCellWitness {
        cell_id,
        old_commitment: [0xAA; 32],
        new_commitment: [0xBB; 32],
        effects_hash,
        timestamp: 0,
        sequence,
        signature: [0xAB; 64],
        cell_state: cell,
        transition_proof: None,
    }
}

fn signed_sovereign_witness(
    cell: &Cell,
    signing_key: &SigningKey,
    old_commitment: [u8; 32],
    effects_hash: [u8; 32],
    sequence: u64,
) -> SovereignCellWitness {
    let cell_id = cell.id();
    let new_commitment = [0u8; 32];
    let timestamp = 0;
    let message = SovereignCellWitness::signing_message(
        &cell_id,
        &old_commitment,
        &new_commitment,
        &effects_hash,
        timestamp,
        sequence,
    );
    SovereignCellWitness {
        cell_id,
        old_commitment,
        new_commitment,
        effects_hash,
        timestamp,
        sequence,
        signature: sign(signing_key, &message).0,
        cell_state: cell.clone(),
        transition_proof: None,
    }
}

fn sovereign_fixture(seed: u8) -> (Ledger, CellId, CellId, Cell, SigningKey, [u8; 32]) {
    let mut ledger = Ledger::new();
    let agent = permissive_cell(1, 1_000);
    let agent_id = agent.id();
    ledger.insert_cell(agent).unwrap();

    let (sovereign, signing_key) = signing_cell(seed, 500);
    let sovereign_id = sovereign.id();
    let old_commitment = sovereign.state_commitment();
    ledger
        .register_sovereign_cell(sovereign_id, old_commitment)
        .unwrap();
    ledger
        .get_mut(&agent_id)
        .unwrap()
        .capabilities
        .grant(sovereign_id, AuthRequired::None);

    (
        ledger,
        agent_id,
        sovereign_id,
        sovereign,
        signing_key,
        old_commitment,
    )
}

// ===========================================================================
// Phase 1: legal witness path
// ===========================================================================

#[test]
fn sovereign_witness_with_legal_key_accepts() {
    let (mut ledger, agent_id, sovereign_id, sovereign, signing_key, old_commitment) =
        sovereign_fixture(2);
    let witness = signed_sovereign_witness(&sovereign, &signing_key, old_commitment, [0u8; 32], 1);
    let mut witnesses = HashMap::new();
    witnesses.insert(sovereign_id, witness);
    let turn = set_field_turn(agent_id, sovereign_id, witnesses);

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
    assert!(
        matches!(&result, TurnResult::Committed { .. }),
        "legal sovereign witness must commit, got: {result:?}"
    );
    assert_eq!(
        ledger.last_sovereign_witness_sequence(&sovereign_id),
        1,
        "committed sovereign witness must advance the replay sequence"
    );
}

#[test]
fn sovereign_witness_with_tampered_key_rejects() {
    let (mut ledger, agent_id, sovereign_id, sovereign, _real_key, old_commitment) =
        sovereign_fixture(2);
    let wrong_key = SigningKey::from_bytes(&[99u8; 32]);
    let witness = signed_sovereign_witness(&sovereign, &wrong_key, old_commitment, [0u8; 32], 1);
    let mut witnesses = HashMap::new();
    witnesses.insert(sovereign_id, witness);
    let turn = set_field_turn(agent_id, sovereign_id, witnesses);

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
    assert!(
        matches!(
            &result,
            TurnResult::Rejected {
                reason: TurnError::InvalidEffect { reason },
                ..
            } if reason.contains("signature")
        ),
        "sovereign witness signed by the wrong key must reject, got: {result:?}"
    );
}

#[test]
fn sovereign_witness_sequence_regression_rejects() {
    let (mut ledger, agent_id, sovereign_id, sovereign, signing_key, old_commitment) =
        sovereign_fixture(3);
    ledger.bump_sovereign_witness_sequence(&sovereign_id, 2);

    let witness = signed_sovereign_witness(&sovereign, &signing_key, old_commitment, [0u8; 32], 1);
    let mut witnesses = HashMap::new();
    witnesses.insert(sovereign_id, witness);
    let turn = set_field_turn(agent_id, sovereign_id, witnesses);

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
    assert!(
        matches!(
            &result,
            TurnResult::Rejected {
                reason: TurnError::InvalidEffect { reason },
                ..
            } if reason.contains("sequence")
        ),
        "regressed sovereign witness sequence must reject, got: {result:?}"
    );
}

// ===========================================================================
// T9: executor cannot skip sovereign witness verification
// ===========================================================================

#[test]
fn sovereign_cell_turn_without_witness_rejects() {
    let mut ledger = Ledger::new();
    let agent = permissive_cell(1, 1_000);
    let agent_id = agent.id();
    ledger.insert_cell(agent).unwrap();

    let sovereign = permissive_cell(2, 500);
    let sovereign_id = sovereign.id();
    ledger
        .register_sovereign_cell(sovereign_id, sovereign.state_commitment())
        .unwrap();

    ledger
        .get_mut(&agent_id)
        .unwrap()
        .capabilities
        .grant(sovereign_id, AuthRequired::None);

    let action = ActionBuilder::new_unchecked_for_tests(sovereign_id, "set_field", agent_id)
        .effect_set_field(sovereign_id, 0, [1u8; 32])
        .build();
    let mut builder = TurnBuilder::new(agent_id, 0);
    builder.add_action(action);
    let turn = builder.fee(0).build();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let result = executor.execute(&turn, &mut ledger);

    assert!(
        matches!(
            &result,
            TurnResult::Rejected {
                reason: TurnError::SovereignWitnessRequired { cell },
                ..
            } if *cell == sovereign_id
        ),
        "sovereign mutation without witness must reject, got: {result:?}"
    );
}

#[test]
#[ignore = "blocked on T9: AIR-side constraint binds the sovereign witness to the cell transition (not just the receipt)"]
fn air_proof_constrains_sovereign_witness_to_transition() {
    // Build a turn with a valid witness payload but mismatched effect
    // (e.g., the witness authorized Transfer(10), the executor applies
    // Transfer(20)). The AIR's per-transition witness check must reject.
    panic!("blocked");
}

// ===========================================================================
// Wire-malleability (T9 tail)
// ===========================================================================

#[test]
fn signing_message_covers_sovereign_witness_payload() {
    let agent = CellId([1u8; 32]);
    let cell = permissive_cell(3, 0);
    let cell_id = cell.id();

    let mut witnesses_a = HashMap::new();
    witnesses_a.insert(
        cell_id,
        dummy_sovereign_witness(cell.clone(), [0x11; 32], 1),
    );
    let turn_a = turn_with_witnesses(agent, witnesses_a);

    let mut witnesses_b = HashMap::new();
    witnesses_b.insert(cell_id, dummy_sovereign_witness(cell, [0x22; 32], 1));
    let turn_b = turn_with_witnesses(agent, witnesses_b);

    assert_ne!(
        turn_a.hash(),
        turn_b.hash(),
        "Turn::hash must change when sovereign witness payload bytes change"
    );

    let msg_a = SovereignCellWitness::signing_message(
        &cell_id,
        &[0xAA; 32],
        &[0xBB; 32],
        &[0x11; 32],
        0,
        1,
    );
    let msg_b = SovereignCellWitness::signing_message(
        &cell_id,
        &[0xAA; 32],
        &[0xBB; 32],
        &[0x22; 32],
        0,
        1,
    );
    assert_ne!(
        msg_a, msg_b,
        "sovereign witness signing message must bind effects_hash payload"
    );
}

#[test]
fn tamper_then_sign_witness_workflow_rejects() {
    let (mut ledger, agent_id, sovereign_id, sovereign, signing_key, old_commitment) =
        sovereign_fixture(7);
    let mut witness =
        signed_sovereign_witness(&sovereign, &signing_key, old_commitment, [0u8; 32], 1);

    witness.effects_hash = [0x44; 32];
    let wrong_key = SigningKey::from_bytes(&[0x55; 32]);
    let message = SovereignCellWitness::signing_message(
        &witness.cell_id,
        &witness.old_commitment,
        &witness.new_commitment,
        &witness.effects_hash,
        witness.timestamp,
        witness.sequence,
    );
    witness.signature = sign(&wrong_key, &message).0;

    let mut witnesses = HashMap::new();
    witnesses.insert(sovereign_id, witness);
    let turn = set_field_turn(agent_id, sovereign_id, witnesses);

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
    assert!(
        matches!(
            &result,
            TurnResult::Rejected {
                reason: TurnError::InvalidEffect { reason },
                ..
            } if reason.contains("signature")
        ),
        "tamper-then-sign with a non-cell key must reject, got: {result:?}"
    );
}

// ===========================================================================
// Cross-cutting: sovereign + bilateral + slot caveats
// ===========================================================================

#[test]
#[ignore = "blocked on sovereign witness AIR teeth + γ.2 + caveat-correctness: full composition"]
fn sovereign_witness_plus_bilateral_transfer_plus_slot_caveats() {
    // Composition mandate — see CAVEAT-LAYER-COVERAGE composition row.
    panic!("blocked");
}

// ===========================================================================
// Sanity: presence of sovereign_witnesses field on Turn does not by itself
// authorize a non-sovereign mutation.
// ===========================================================================

// ===========================================================================
// Extended adversarial scenarios (Phase 1 + AIR teeth)
// ===========================================================================

#[test]
fn sovereign_witness_cross_cell_reuse_rejects() {
    let (mut ledger, agent_id, alice_id, alice, alice_key, alice_old_commitment) =
        sovereign_fixture(4);
    let (bob, _bob_key) = signing_cell(5, 500);
    let bob_id = bob.id();
    ledger
        .register_sovereign_cell(bob_id, bob.state_commitment())
        .unwrap();
    ledger
        .get_mut(&agent_id)
        .unwrap()
        .capabilities
        .grant(bob_id, AuthRequired::None);

    let alice_witness =
        signed_sovereign_witness(&alice, &alice_key, alice_old_commitment, [0u8; 32], 1);
    let mut witnesses = HashMap::new();
    witnesses.insert(bob_id, alice_witness);
    let turn = set_field_turn(agent_id, bob_id, witnesses);

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
    assert!(
        matches!(
            &result,
            TurnResult::Rejected {
                reason: TurnError::InvalidEffect { reason },
                ..
            } if reason.contains("payload cell_id")
        ),
        "witness for {alice_id} reused under {bob_id} must reject, got: {result:?}"
    );
}

#[test]
fn sovereign_witness_exact_replay_rejects() {
    let (mut ledger, agent_id, sovereign_id, sovereign, signing_key, old_commitment) =
        sovereign_fixture(8);
    let witness = signed_sovereign_witness(&sovereign, &signing_key, old_commitment, [0u8; 32], 1);

    let mut first_witnesses = HashMap::new();
    first_witnesses.insert(sovereign_id, witness.clone());
    let first = set_field_turn(agent_id, sovereign_id, first_witnesses);
    let first_result = TurnExecutor::new(ComputronCosts::zero()).execute(&first, &mut ledger);
    assert!(
        matches!(&first_result, TurnResult::Committed { .. }),
        "initial witness use must commit before replay check, got: {first_result:?}"
    );

    let mut replay_witnesses = HashMap::new();
    replay_witnesses.insert(sovereign_id, witness);
    let mut replay = set_field_turn(agent_id, sovereign_id, replay_witnesses);
    replay.nonce = 1;

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&replay, &mut ledger);
    let rejected_as_replay = matches!(
        &result,
        TurnResult::Rejected {
            reason: TurnError::SovereignCommitmentMismatch { .. },
            ..
        }
    ) || matches!(
        &result,
        TurnResult::Rejected {
            reason: TurnError::InvalidEffect { reason },
            ..
        } if reason.contains("sequence")
    );
    assert!(
        rejected_as_replay,
        "exact sovereign witness replay must reject before commit, got: {result:?}"
    );
}

#[test]
fn sovereign_witness_after_key_rotation_old_key_rejects() {
    let mut ledger = Ledger::new();
    let agent = permissive_cell(1, 1_000);
    let agent_id = agent.id();
    ledger.insert_cell(agent).unwrap();

    let (old_cell, old_key) = signing_cell(9, 500);
    let old_id = old_cell.id();
    let new_key = SigningKey::from_bytes(&[0x99; 32]);
    let mut rotated =
        Cell::remote_stub_with_id_pk_balance(old_id, *new_key.public_key().as_bytes(), 500);
    rotated.permissions = old_cell.permissions.clone();
    let old_commitment = rotated.state_commitment();
    ledger
        .register_sovereign_cell(old_id, old_commitment)
        .unwrap();
    ledger
        .get_mut(&agent_id)
        .unwrap()
        .capabilities
        .grant(old_id, AuthRequired::None);

    let witness = signed_sovereign_witness(&rotated, &old_key, old_commitment, [0u8; 32], 1);
    let mut witnesses = HashMap::new();
    witnesses.insert(old_id, witness);
    let turn = set_field_turn(agent_id, old_id, witnesses);

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
    assert!(
        matches!(
            &result,
            TurnResult::Rejected {
                reason: TurnError::InvalidEffect { reason },
                ..
            } if reason.contains("signature")
        ),
        "old key must not sign for rotated sovereign cell key, got: {result:?}"
    );
}

#[test]
fn sovereign_witness_equal_sequence_rejects() {
    let (mut ledger, agent_id, sovereign_id, sovereign, signing_key, old_commitment) =
        sovereign_fixture(3);
    ledger.bump_sovereign_witness_sequence(&sovereign_id, 1);

    let witness = signed_sovereign_witness(&sovereign, &signing_key, old_commitment, [0u8; 32], 1);
    let mut witnesses = HashMap::new();
    witnesses.insert(sovereign_id, witness);
    let turn = set_field_turn(agent_id, sovereign_id, witnesses);

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
    assert!(
        matches!(
            &result,
            TurnResult::Rejected {
                reason: TurnError::InvalidEffect { reason },
                ..
            } if reason.contains("sequence")
        ),
        "sovereign witness with sequence equal to current must reject, got: {result:?}"
    );
}

#[test]
fn sovereign_witness_payload_tamper_with_intact_signature_rejects() {
    let (mut ledger, agent_id, sovereign_id, sovereign, signing_key, old_commitment) =
        sovereign_fixture(6);
    let mut witness =
        signed_sovereign_witness(&sovereign, &signing_key, old_commitment, [0u8; 32], 1);
    witness.effects_hash = [0xEF; 32];
    let mut witnesses = HashMap::new();
    witnesses.insert(sovereign_id, witness);
    let turn = set_field_turn(agent_id, sovereign_id, witnesses);

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
    assert!(
        matches!(
            &result,
            TurnResult::Rejected {
                reason: TurnError::InvalidEffect { reason },
                ..
            } if reason.contains("signature")
        ),
        "payload tamper after signing must reject, got: {result:?}"
    );
}

#[test]
fn turn_with_two_sovereign_cells_one_witness_invalid_rejects() {
    let (mut ledger, agent_id, alice_id, alice, alice_key, alice_old_commitment) =
        sovereign_fixture(10);
    let (bob, _bob_key) = signing_cell(11, 500);
    let bob_id = bob.id();
    let bob_old_commitment = bob.state_commitment();
    ledger
        .register_sovereign_cell(bob_id, bob_old_commitment)
        .unwrap();
    ledger
        .get_mut(&agent_id)
        .unwrap()
        .capabilities
        .grant(bob_id, AuthRequired::None);

    let alice_witness =
        signed_sovereign_witness(&alice, &alice_key, alice_old_commitment, [0u8; 32], 1);
    let wrong_key = SigningKey::from_bytes(&[0xAA; 32]);
    let bob_witness = signed_sovereign_witness(&bob, &wrong_key, bob_old_commitment, [0u8; 32], 1);

    let mut witnesses = HashMap::new();
    witnesses.insert(alice_id, alice_witness);
    witnesses.insert(bob_id, bob_witness);
    let turn = two_set_field_turn(agent_id, alice_id, bob_id, witnesses);

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
    assert!(
        matches!(
            &result,
            TurnResult::Rejected {
                reason: TurnError::InvalidEffect { reason },
                ..
            } if reason.contains("signature")
        ),
        "one invalid sovereign witness must reject the whole turn, got: {result:?}"
    );
}

#[test]
fn extra_witness_for_non_sovereign_cell_does_not_grant_authorization() {
    let mut ledger = Ledger::new();
    let agent = permissive_cell(1, 1_000);
    let agent_id = agent.id();
    ledger.insert_cell(agent).unwrap();

    let (hosted, hosted_key) = signing_cell(12, 500);
    let hosted_id = hosted.id();
    let hosted_commitment = hosted.state_commitment();
    ledger.insert_cell(hosted.clone()).unwrap();

    let witness = signed_sovereign_witness(&hosted, &hosted_key, hosted_commitment, [0u8; 32], 1);
    let mut witnesses = HashMap::new();
    witnesses.insert(hosted_id, witness);
    let turn = set_field_turn(agent_id, hosted_id, witnesses);

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
    assert!(
        matches!(
            &result,
            TurnResult::Rejected {
                reason: TurnError::InvalidEffect { reason },
                ..
            } if reason.contains("non-sovereign")
        ),
        "extra witness for hosted cell must not grant authorization, got: {result:?}"
    );
}

#[test]
#[ignore = "blocked on sovereign-witness AIR teeth: tx-time vs verify-time consistency — the witness's sequence number bound in the AIR PI must equal the sequence number in the witness payload AND in the on-chain cell state"]
fn sovereign_witness_sequence_pi_state_payload_must_agree() {
    panic!("blocked");
}

// ===========================================================================
// Composition: sovereign witness + slot caveats
// ===========================================================================

#[test]
fn sovereign_cell_slot_caveats_still_fire() {
    let (mut ledger, agent_id, sovereign_id, mut sovereign, signing_key, _) = sovereign_fixture(13);
    sovereign.program = CellProgram::Predicate(vec![StateConstraint::Monotonic { index: 0 }]);
    sovereign.state.set_field(0, field_from_u64(10));
    let old_commitment = sovereign.state_commitment();
    ledger
        .update_sovereign_commitment(&sovereign_id, old_commitment)
        .unwrap();

    let witness = signed_sovereign_witness(&sovereign, &signing_key, old_commitment, [0u8; 32], 1);
    let mut witnesses = HashMap::new();
    witnesses.insert(sovereign_id, witness);
    let turn = set_field_turn_with_action_witnesses(
        agent_id,
        sovereign_id,
        witnesses,
        0,
        field_from_u64(9),
        vec![],
    );

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
    assert!(
        matches!(
            &result,
            TurnResult::Rejected {
                reason: TurnError::ProgramViolation { .. },
                ..
            }
        ),
        "sovereign witness must not bypass Monotonic slot caveat, got: {result:?}"
    );
}

#[test]
fn sovereign_with_preimage_gate_requires_both_witnesses() {
    let (mut ledger, agent_id, sovereign_id, mut sovereign, signing_key, _) = sovereign_fixture(14);
    let preimage = [0x42; 32];
    let commitment = *blake3::hash(&preimage).as_bytes();
    sovereign.program = CellProgram::Predicate(vec![StateConstraint::PreimageGate {
        commitment_index: 0,
        hash_kind: dregg_cell::program::HashKind::Blake3,
    }]);
    let old_commitment = sovereign.state_commitment();
    ledger
        .update_sovereign_commitment(&sovereign_id, old_commitment)
        .unwrap();

    let witness = signed_sovereign_witness(&sovereign, &signing_key, old_commitment, [0u8; 32], 1);
    let mut missing_preimage_witnesses = HashMap::new();
    missing_preimage_witnesses.insert(sovereign_id, witness.clone());
    let missing_preimage = set_field_turn_with_action_witnesses(
        agent_id,
        sovereign_id,
        missing_preimage_witnesses,
        0,
        commitment,
        vec![],
    );

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&missing_preimage, &mut ledger);
    assert!(
        matches!(
            &result,
            TurnResult::Rejected {
                reason: TurnError::ProgramViolation { .. },
                ..
            }
        ),
        "sovereign witness alone must not satisfy PreimageGate, got: {result:?}"
    );

    let mut witnesses = HashMap::new();
    witnesses.insert(sovereign_id, witness);
    let mut with_preimage = set_field_turn_with_action_witnesses(
        agent_id,
        sovereign_id,
        witnesses,
        0,
        commitment,
        vec![WitnessBlob::preimage(preimage)],
    );
    with_preimage.nonce = 1;

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&with_preimage, &mut ledger);
    assert!(
        matches!(&result, TurnResult::Committed { .. }),
        "sovereign witness plus PreimageGate witness should commit, got: {result:?}"
    );
}

// ===========================================================================
// Sovereign + cross-federation
// ===========================================================================

#[test]
#[ignore = "blocked on sovereign-witness AIR teeth + cross-federation: sovereign witness signed for federation F1 presented in F2 must reject; the witness payload includes federation_id (per AUDIT-federation.md F1/F2 closure expectation)"]
fn sovereign_witness_cross_federation_replay_rejects() {
    panic!("blocked");
}

// ===========================================================================
// Sanity: Turn::hash covers the sovereign_witnesses field
// ===========================================================================

#[test]
fn sovereign_witnesses_field_is_covered_by_turn_hash() {
    let agent = CellId([1u8; 32]);

    let empty = turn_with_witnesses(agent, HashMap::new());

    // Construct a non-empty witness — bytes only need to differ from the
    // default for the hash check (we're NOT validating the witness's
    // signature here, only that Turn::hash sees the witness map).
    let cell_pk = [0xCA; 32];
    let cell = Cell::with_balance(cell_pk, [0u8; 32], 0);
    let cell_id = cell.id();
    let mut witnesses = HashMap::new();
    let w = SovereignCellWitness {
        cell_id,
        old_commitment: [0xAA; 32],
        new_commitment: [0xBB; 32],
        effects_hash: [0xCC; 32],
        timestamp: 0,
        sequence: 1,
        signature: [0xAB; 64],
        cell_state: cell,
        transition_proof: None,
    };
    witnesses.insert(cell_id, w);
    let with_witness = turn_with_witnesses(agent, witnesses);

    assert_ne!(
        empty.hash(),
        with_witness.hash(),
        "Turn::hash MUST cover sovereign_witnesses — see EXECUTOR-HONESTY-AUDIT.md T9 wire-malleability"
    );

    // SovereignCellWitness::signing_message must be a publicly callable
    // function so verifier-side replay can recompute the signing
    // message and reject witnesses whose payload was tampered.
    let msg = SovereignCellWitness::signing_message(
        &cell_id,
        &[0xAA; 32],
        &[0xBB; 32],
        &[0xCC; 32],
        0,
        1,
    );
    assert!(
        msg.starts_with(b"dregg-sovereign-witness-v1:"),
        "signing message must begin with the v1 domain separator"
    );
}

#[test]
fn turn_sovereign_witnesses_field_is_a_map_and_constructs_empty() {
    use dregg_turn::Turn;
    use std::collections::HashMap;
    let agent = CellId([1u8; 32]);
    let turn = Turn {
        agent,
        nonce: 0,
        call_forest: dregg_turn::CallForest::new(),
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    };
    assert!(turn.sovereign_witnesses.is_empty());
}
