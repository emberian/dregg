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

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::{
    ActionBuilder, ComputronCosts, SovereignCellWitness, Turn, TurnBuilder, TurnError,
    TurnExecutor, TurnResult,
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
    let action = ActionBuilder::new_unchecked_for_tests(target, "set_field", agent)
        .effect_set_field(target, 0, [1u8; 32])
        .build();
    let mut builder = TurnBuilder::new(agent, 0);
    builder.add_action(action);
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
#[ignore = "blocked on SOVEREIGN-WITNESS-AIR-DESIGN.md Phase 1: AIR algebraically constrains sovereign witness (currently only decorates the receipt per AUDIT-sovereign-witness-teeth.md)"]
fn sovereign_witness_with_legal_key_accepts() {
    // Build a sovereign cell, sign a witness payload with its key, attach
    // to a turn, execute. Expect Committed + proof verifies.
    panic!("blocked");
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
#[ignore = "blocked on sovereign-witness AIR teeth: witness sequence regression must reject"]
fn sovereign_witness_sequence_regression_rejects() {
    // Two turns with sovereign witnesses; the second turn's witness sequence
    // must be > the first's.
    panic!("blocked");
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
#[ignore = "blocked on wire-malleability: tamper-then-sign workflow (attacker mutates witness AFTER signing, recomputes signature) — should still reject because re-signing requires the cell key"]
fn tamper_then_sign_witness_workflow_rejects() {
    panic!("blocked");
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
#[ignore = "blocked on sovereign-witness AIR teeth + verifier-replay: a sovereign witness signed for cell A presented on a turn that mutates cell B (cross-cell reuse) must reject"]
fn sovereign_witness_cross_cell_reuse_rejects() {
    // The cell_id is part of what the witness signs; presenting Alice's
    // signed witness on a turn that targets Bob's cell must fail because
    // the witness payload says "for cell A" but the executor is
    // applying it to cell B.
    panic!("blocked");
}

#[test]
#[ignore = "blocked on sovereign-witness AIR teeth: replaying the EXACT same witness payload (same sequence, same cell, same effect) twice must reject the second occurrence — sequence must strictly increase"]
fn sovereign_witness_exact_replay_rejects() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on sovereign-witness AIR teeth: witness signed under an OLD key after the cell rotated keys must reject (per-key rotation seq number bound into witness payload)"]
fn sovereign_witness_after_key_rotation_old_key_rejects() {
    panic!("blocked");
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
#[ignore = "blocked on sovereign-witness AIR teeth: tampered witness payload (modify the effect bytes, leave signature valid for old payload) must reject — signature recomputation must require the cell key"]
fn sovereign_witness_payload_tamper_with_intact_signature_rejects() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on sovereign-witness AIR teeth: two sovereign cells in one turn, both witnessed — if EITHER witness is invalid, the whole turn must reject"]
fn turn_with_two_sovereign_cells_one_witness_invalid_rejects() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on sovereign-witness AIR teeth: a turn with sovereign_witnesses populated for a NON-sovereign cell — the extra witness must be ignored (not cause acceptance for a non-sovereign mutation that lacked normal authorization)"]
fn extra_witness_for_non_sovereign_cell_does_not_grant_authorization() {
    panic!("blocked");
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
#[ignore = "blocked on sovereign-witness AIR teeth + caveat-correctness: sovereign cell with Monotonic slot caveat — the witness authorizes the effect, but the slot caveat must fire INDEPENDENTLY (sovereign mode bypasses normal Authorization but NOT slot caveats)"]
fn sovereign_cell_slot_caveats_still_fire() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on sovereign-witness AIR teeth + caveat-correctness: sovereign cell with PreimageGate slot caveat — sovereign witness authorizes the action, but the preimage gate also requires a fresh-reveal witness, distinct from the sovereign witness"]
fn sovereign_with_preimage_gate_requires_both_witnesses() {
    panic!("blocked");
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
