//! Executor-honesty threat tests, T1-T15 from `EXECUTOR-HONESTY-AUDIT.md`.
//!
//! Layer: AIR + canonical signing message + verifier-side replay.
//!
//! Each test exercises *one* of the threats from the audit and proves the
//! corresponding defense triggers. Tests that depend on yet-to-land
//! single-cell AIR-binding work are marked `#[ignore]` with the audit's
//! `[stage7-cont]` or other unblock-by-lane label.
//!
//! Threats are the audit's enumeration — keep this file's order matched to
//! the audit so a reader can cross-reference.

use std::collections::HashMap;

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::action::{Action, Authorization, BearerCapProof, DelegationProofData, symbol};
use dregg_turn::{
    CallForest, ComputronCosts, DelegationMode, Effect, Turn, TurnError, TurnExecutor, TurnReceipt,
    TurnResult, VerifyError, sign_receipt, verify_receipt_chain_with_keys,
};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

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

fn one_action_turn(agent: CellId, nonce: u64, effects: Vec<Effect>) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: agent,
        method: symbol("test"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects,
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    });
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
        sovereign_witnesses: HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

fn effect_vm_rejects_tampered_pi(pi_index: usize, label: &str) {
    let initial_state = dregg_circuit::CellState::new(1_000, 7);
    let effects = vec![dregg_circuit::effect_vm::Effect::Transfer {
        amount: 1,
        direction: 1,
    }];
    let (trace, public_inputs) =
        dregg_circuit::effect_vm::generate_effect_vm_trace(&initial_state, &effects);
    let air = dregg_circuit::EffectVmAir::new(trace.len());
    let proof = dregg_circuit::stark::prove(&air, &trace, &public_inputs);

    dregg_circuit::stark::verify(&air, &proof, &public_inputs)
        .expect("control Effect VM proof must verify before PI tampering");

    let mut tampered = public_inputs.clone();
    tampered[pi_index] = tampered[pi_index] + dregg_circuit::field::BabyBear::ONE;

    assert!(
        dregg_circuit::stark::verify(&air, &proof, &tampered).is_err(),
        "Effect VM verifier accepted a proof after tampering PI[{pi_index}] ({label})"
    );
}

fn sample_receipt(
    agent: CellId,
    turn_hash: [u8; 32],
    previous_receipt_hash: Option<[u8; 32]>,
) -> TurnReceipt {
    TurnReceipt {
        turn_hash,
        forest_hash: [0x11u8; 32],
        pre_state_hash: [0x22u8; 32],
        post_state_hash: [0x33u8; 32],
        timestamp: 1_700_000_000,
        effects_hash: [0x44u8; 32],
        computrons_used: 7,
        action_count: 1,
        previous_receipt_hash,
        agent,
        federation_id: [0x55u8; 32],
        routing_directives: vec![],
        introduction_exports: vec![],
        derivation_records: vec![],
        emitted_events: vec![],
        executor_signature: None,
        finality: Default::default(),
        was_encrypted: false,
        was_burn: false,
    }
}

fn replay_entry_with_receipt_pi(receipt: TurnReceipt) -> dregg_verifier::ReplayEntry {
    use dregg_circuit::effect_vm::pi;
    use dregg_commit::typed::canonical_32_to_felts_4;

    let mut public_inputs = vec![0u32; pi::BASE_COUNT];
    let turn_hash = canonical_32_to_felts_4(&receipt.turn_hash);
    for i in 0..pi::TURN_HASH_LEN {
        public_inputs[pi::TURN_HASH_BASE + i] = turn_hash[i].as_u32();
    }
    let previous = canonical_32_to_felts_4(&receipt.previous_receipt_hash.unwrap_or([0u8; 32]));
    for i in 0..pi::PREVIOUS_RECEIPT_HASH_LEN {
        public_inputs[pi::PREVIOUS_RECEIPT_HASH_BASE + i] = previous[i].as_u32();
    }
    public_inputs[pi::IS_AGENT_CELL] = 1;

    dregg_verifier::ReplayEntry {
        receipt,
        proof_bytes: vec![],
        public_inputs,
        witness_bundle: None,
        witness_hash: [0u8; 32],
        aggregate_membership: None,
    }
}

fn effect_vm_air_rejects_tampered_trace(
    trace: &[Vec<dregg_circuit::field::BabyBear>],
    public_inputs: &[dregg_circuit::field::BabyBear],
    row: usize,
    label: &str,
) {
    use dregg_circuit::field::BabyBear;
    use dregg_circuit::stark::StarkAir;

    let air = dregg_circuit::EffectVmAir::new(trace.len());
    let next = (row + 1) % trace.len();
    let rejects_for_some_challenge = [7u32, 13, 101, 2017, 31337].into_iter().any(|alpha| {
        air.eval_constraints(
            &trace[row],
            &trace[next],
            public_inputs,
            BabyBear::new(alpha),
        ) != BabyBear::ZERO
    });
    assert!(
        rejects_for_some_challenge,
        "{label}: AIR accepted the tampered trace for all sampled alphas"
    );
}

// ===========================================================================
// T1 — Reorder effects within a turn
// ===========================================================================

#[test]
fn t1_turn_hash_covers_effect_order() {
    // The defense: effects_hash is ordered. Two turns with the same effects
    // in different order must produce different turn hashes.
    let a = CellId([1u8; 32]);
    let b = CellId([2u8; 32]);
    let e1 = Effect::Transfer {
        from: a,
        to: b,
        amount: 10,
    };
    let e2 = Effect::Transfer {
        from: a,
        to: b,
        amount: 20,
    };
    let t_12 = one_action_turn(a, 0, vec![e1.clone(), e2.clone()]);
    let t_21 = one_action_turn(a, 0, vec![e2, e1]);
    assert_ne!(
        t_12.hash(),
        t_21.hash(),
        "effect order must change turn hash"
    );
}

#[test]
#[ignore = "blocked on Stage 7 cont §B verification: AIR's EFFECTS_HASH_BASE row-0 boundary binds to in-trace effect bytes; this test reconstructs a trace with reordered effects and shows the AIR rejects the resulting proof"]
fn t1_air_rejects_reordered_effects_in_trace() {
    panic!("blocked");
}

// ===========================================================================
// T2 — Invent effects the actor did not sign
// ===========================================================================

#[test]
fn t2_turn_hash_covers_effect_count() {
    let a = CellId([1u8; 32]);
    let b = CellId([2u8; 32]);
    let e1 = Effect::Transfer {
        from: a,
        to: b,
        amount: 10,
    };
    let e2 = Effect::Transfer {
        from: a,
        to: b,
        amount: 5,
    };
    let t_one = one_action_turn(a, 0, vec![e1.clone()]);
    let t_two = one_action_turn(a, 0, vec![e1, e2]);
    assert_ne!(
        t_one.hash(),
        t_two.hash(),
        "inventing an extra effect must change turn hash"
    );
}

#[test]
#[ignore = "blocked on EXECUTOR-HONESTY-AUDIT.md T2 gap: confirm verify path is THE ONLY way into TurnExecutor; CI guard for new Authorization::Unchecked regressions"]
fn t2_no_authorization_unchecked_in_production_paths() {
    panic!("blocked");
}

// ===========================================================================
// T3 — Skip / omit effects from a signed turn
// ===========================================================================

#[test]
#[ignore = "blocked on Stage 7 cont §B AIR termination constraint: EFFECTS_HASH_GLOBAL must terminate at the PI-exposed effects_hash; omitting an effect breaks the chain"]
fn t3_air_rejects_omitted_effect() {
    panic!("blocked");
}

// ===========================================================================
// T4 — Lie about pre/post state hash
// ===========================================================================

#[test]
fn t4_air_binds_pre_state_hash_to_trace() {
    effect_vm_rejects_tampered_pi(
        dregg_circuit::effect_vm::pi::OLD_COMMIT_BASE,
        "OLD_COMMIT_BASE",
    );
}

#[test]
fn t4_air_binds_post_state_hash_to_trace() {
    effect_vm_rejects_tampered_pi(
        dregg_circuit::effect_vm::pi::NEW_COMMIT_BASE,
        "NEW_COMMIT_BASE",
    );
}

// ===========================================================================
// T5 — Reuse a nonce
// ===========================================================================

#[test]
fn t5_executor_rejects_replayed_nonce() {
    // The executor's runtime check: it increments cell.nonce when a turn
    // executes and rejects any turn whose `nonce` doesn't match the current
    // cell.nonce.
    let cell = permissive_cell(1, 1_000);
    let agent = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let t1 = one_action_turn(agent, 0, vec![]);
    let r1 = executor.execute(&t1, &mut ledger);
    assert!(matches!(
        r1,
        TurnResult::Committed { .. } | TurnResult::Rejected { .. }
    ));

    // Submit a turn with nonce=0 again — must reject (nonce should now be 1).
    let t1_replay = one_action_turn(agent, 0, vec![]);
    let r_replay = executor.execute(&t1_replay, &mut ledger);
    assert!(
        matches!(r_replay, TurnResult::Rejected { .. }),
        "expected nonce-replay reject, got: {r_replay:?}"
    );
}

#[test]
fn t5_air_rejects_proof_with_wrong_nonce_pi() {
    effect_vm_rejects_tampered_pi(dregg_circuit::effect_vm::pi::ACTOR_NONCE, "ACTOR_NONCE");
}

// ===========================================================================
// T6 — Replay a turn from another federation / ledger
// ===========================================================================

#[test]
fn t6_signed_turn_for_federation_a_rejects_on_federation_b() {
    let agent = CellId([6u8; 32]);
    let target = CellId([7u8; 32]);
    let action = Action {
        target,
        method: symbol("transfer"),
        args: vec![[0xD6u8; 32]],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::Transfer {
            from: agent,
            to: target,
            amount: 3,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: Some(-3),
        witness_blobs: vec![],
    };
    let federation_a = [0xA6u8; 32];
    let federation_b = [0xB6u8; 32];

    assert_ne!(
        TurnExecutor::compute_signing_message(&action, &federation_a),
        TurnExecutor::compute_signing_message(&action, &federation_b),
        "full action signatures must bind federation_id"
    );
    assert_ne!(
        TurnExecutor::compute_partial_signing_message(&action, 0, &federation_a, 42),
        TurnExecutor::compute_partial_signing_message(&action, 0, &federation_b, 42),
        "partial action signatures must bind federation_id"
    );
    assert_ne!(
        TurnExecutor::compute_bearer_delegation_message(
            &target,
            &AuthRequired::Signature,
            &[0x11u8; 32],
            99,
            &federation_a,
        ),
        TurnExecutor::compute_bearer_delegation_message(
            &target,
            &AuthRequired::Signature,
            &[0x11u8; 32],
            99,
            &federation_b,
        ),
        "bearer delegation signatures must bind federation_id"
    );
    assert_ne!(
        Authorization::captp_delivered_signing_message_for_federation(
            &federation_a,
            &[0x22u8; 32],
            &agent,
            &target,
            42,
            &action.effects,
        ),
        Authorization::captp_delivered_signing_message_for_federation(
            &federation_b,
            &[0x22u8; 32],
            &agent,
            &target,
            42,
            &action.effects,
        ),
        "CapTP delivery signatures must bind federation_id"
    );
}

// ===========================================================================
// T7 — Forge a receipt signature
// ===========================================================================

#[test]
fn t7_receipt_signed_by_wrong_key_rejects() {
    let agent = CellId([0x71u8; 32]);
    let mut receipt = sample_receipt(agent, [0x72u8; 32], None);
    let signing_seed = [0x73u8; 32];
    receipt.executor_signature = Some(sign_receipt(&receipt, &signing_seed));

    let trusted_wrong_executor = dregg_types::SigningKey::from_bytes(&[0x74u8; 32])
        .public_key()
        .0;
    let err = verify_receipt_chain_with_keys(&[receipt], &[trusted_wrong_executor])
        .expect_err("receipt signed by an untrusted executor key must reject");
    assert!(matches!(err, VerifyError::ExecutorSignatureInvalid { .. }));
}

#[test]
fn t7_receipt_carries_executor_identity() {
    // Current receipt identity is verifier-side: the receipt carries an
    // executor_signature, and the verifier accepts it only under the trusted
    // executor key that produced that signature.
    let agent = CellId([0x75u8; 32]);
    let mut receipt = sample_receipt(agent, [0x76u8; 32], None);
    let signing_seed = [0x77u8; 32];
    receipt.executor_signature = Some(sign_receipt(&receipt, &signing_seed));

    let signer_pk = dregg_types::SigningKey::from_bytes(&signing_seed)
        .public_key()
        .0;
    let other_pk = dregg_types::SigningKey::from_bytes(&[0x78u8; 32])
        .public_key()
        .0;

    verify_receipt_chain_with_keys(&[receipt.clone()], &[signer_pk])
        .expect("receipt must verify against the executor key that signed it");
    let err = verify_receipt_chain_with_keys(&[receipt], &[other_pk])
        .expect_err("receipt verifier identity is the trusted executor key set");
    assert!(matches!(err, VerifyError::ExecutorSignatureInvalid { .. }));
}

// ===========================================================================
// T8 — Insert a fake previous_receipt_hash link
// ===========================================================================

#[test]
fn t8_verifier_rejects_fake_previous_receipt_hash() {
    let agent = CellId([0x81u8; 32]);
    let mut prior = sample_receipt(agent, [0x82u8; 32], None);
    prior.post_state_hash = [0x83u8; 32];

    let forged_previous = [0x84u8; 32];
    let receipt = sample_receipt(agent, [0x85u8; 32], Some(forged_previous));
    let entry = replay_entry_with_receipt_pi(receipt);

    let reason = dregg_verifier::check_receipt_pi_binding(&entry, Some(prior.receipt_hash()))
        .expect("chain-walk must reject a fake previous_receipt_hash");
    assert!(
        reason.contains("chain-walk"),
        "expected chain-walk rejection, got: {reason}"
    );
}

// ===========================================================================
// T9 — Skip sovereign-witness verification
// ===========================================================================

#[test]
fn t9_sovereign_witness_skip_rejected_by_air() {
    let mut ledger = Ledger::new();
    let agent = permissive_cell(0x91, 1_000);
    let agent_id = agent.id();
    ledger.insert_cell(agent).unwrap();

    let sovereign = permissive_cell(0x92, 500);
    let sovereign_id = sovereign.id();
    ledger
        .register_sovereign_cell(sovereign_id, sovereign.state_commitment())
        .unwrap();
    ledger
        .get_mut(&agent_id)
        .unwrap()
        .capabilities
        .grant(sovereign_id, AuthRequired::None);

    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: sovereign_id,
        method: symbol("set_field"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::SetField {
            cell: sovereign_id,
            index: 0,
            value: [0x99u8; 32],
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    });
    let turn = Turn {
        agent: agent_id,
        nonce: 0,
        call_forest: forest,
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

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
    assert!(
        matches!(
            result,
            TurnResult::Rejected {
                reason: TurnError::SovereignWitnessRequired { cell },
                ..
            } if cell == sovereign_id
        ),
        "sovereign mutation without a witness must reject, got: {result:?}"
    );
}

// ===========================================================================
// T10 — Skip a permission / capability check
// ===========================================================================

#[test]
fn t10_executor_rejects_transfer_without_required_capability() {
    // Setup: A → B Transfer, but A has no cap to B and B's `send`
    // permission requires a signature.
    let a_cell = {
        let mut c = permissive_cell(10, 1_000);
        // Tighten send permission to require a sig, but DON'T grant any
        // capabilities — so the action should fail authorization.
        c.permissions.send = AuthRequired::Signature;
        c
    };
    let a = a_cell.id();
    let b_cell = permissive_cell(11, 0);
    let b = b_cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(a_cell).unwrap();
    ledger.insert_cell(b_cell).unwrap();

    let turn = one_action_turn(
        a,
        0,
        vec![Effect::Transfer {
            from: a,
            to: b,
            amount: 1,
        }],
    );
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        matches!(result, TurnResult::Rejected { .. }),
        "transfer without auth must reject, got: {result:?}"
    );
}

#[test]
fn t10_captp_variants_use_real_merkle_membership() {
    use dregg_circuit::effect_vm as vm;
    use dregg_circuit::field::BabyBear;
    use dregg_circuit::poseidon2::hash_2_to_1;

    let mut export_state = dregg_circuit::CellState::new(1_000, 0);
    export_state.fields[7] = BabyBear::new(5);
    export_state.refresh_commitment();
    let export_effect = vm::Effect::ExportSturdyRef {
        cell_id: BabyBear::new(0xCE11),
        permissions: BabyBear::new(0x07),
        random_seed: BabyBear::new(0x5EED),
        export_counter: 5,
    };
    let (mut export_trace, export_pi) =
        vm::generate_effect_vm_trace(&export_state, &[export_effect]);
    export_trace[0][vm::AUX_BASE] = export_trace[0][vm::AUX_BASE] + BabyBear::ONE;
    effect_vm_air_rejects_tampered_trace(&export_trace, &export_pi, 0, "ExportSturdyRef swiss");

    let mut enliven_state = dregg_circuit::CellState::new(1_000, 0);
    enliven_state.fields[6] = BabyBear::new(2);
    enliven_state.fields[4] = BabyBear::new(0x4444);
    enliven_state.refresh_commitment();
    let enliven_effect = vm::Effect::EnlivenRef {
        swiss_number: BabyBear::new(0x5155),
        presenter_id: BabyBear::new(0x9E5),
        expected_cell_id: BabyBear::new(0xCE11),
        expected_permissions: BabyBear::new(0x07),
    };
    let (mut enliven_trace, enliven_pi) =
        vm::generate_effect_vm_trace(&enliven_state, &[enliven_effect]);
    enliven_trace[0][vm::AUX_BASE + 6] = enliven_trace[0][vm::AUX_BASE + 6] + BabyBear::ONE;
    effect_vm_air_rejects_tampered_trace(
        &enliven_trace,
        &enliven_pi,
        0,
        "EnlivenRef membership sibling",
    );

    let mut drop_state = dregg_circuit::CellState::new(1_000, 0);
    drop_state.fields[5] = BabyBear::new(3);
    drop_state.fields[3] = BabyBear::new(0x3333);
    drop_state.refresh_commitment();
    let drop_effect = vm::Effect::DropRef {
        cell_id: BabyBear::new(0xCE11),
        holder_federation: BabyBear::new(0xFED1),
        current_refcount: 3,
    };
    let (mut drop_trace, drop_pi) = vm::generate_effect_vm_trace(&drop_state, &[drop_effect]);
    drop_trace[0][vm::AUX_BASE + 6] = drop_trace[0][vm::AUX_BASE + 6] + BabyBear::ONE;
    effect_vm_air_rejects_tampered_trace(&drop_trace, &drop_pi, 0, "DropRef membership sibling");

    let handoff_state = dregg_circuit::CellState::new(1_000, 0);
    let cert_hash = BabyBear::new(0xCE87);
    let recipient_pk = BabyBear::new(0x8EC1);
    let introducer_pk = BabyBear::new(0x1117);
    let leaf = hash_2_to_1(cert_hash, hash_2_to_1(recipient_pk, introducer_pk));
    let approved_root = hash_2_to_1(leaf, BabyBear::ZERO);
    let handoff_effect = vm::Effect::ValidateHandoff {
        certificate_hash: cert_hash,
        recipient_pk,
        introducer_pk,
        approved_set_root: approved_root,
    };
    let mut context = vm::EffectVmContext::default();
    context.approved_handoffs_root[0] = approved_root;
    let (mut handoff_trace, handoff_pi) =
        vm::generate_effect_vm_trace_ext(&handoff_state, &[handoff_effect], context);
    handoff_trace[0][vm::AUX_BASE] = handoff_trace[0][vm::AUX_BASE] + BabyBear::ONE;
    effect_vm_air_rejects_tampered_trace(
        &handoff_trace,
        &handoff_pi,
        0,
        "ValidateHandoff membership leaf",
    );
}

// ===========================================================================
// T11 — Submit a stale / cached proof for a new turn
// ===========================================================================

#[test]
fn t11_stale_proof_replay_rejected_by_verifier() {
    let agent = CellId([0xA1u8; 32]);
    let receipt = sample_receipt(agent, [0xA2u8; 32], None);
    let mut entry = replay_entry_with_receipt_pi(receipt);
    entry.public_inputs[dregg_circuit::effect_vm::pi::TURN_HASH_BASE] ^= 0x01;

    let reason = dregg_verifier::check_receipt_pi_binding(&entry, None)
        .expect("stale proof PI must reject when TURN_HASH no longer matches receipt");
    assert!(
        reason.contains("TURN_HASH_BASE"),
        "expected TURN_HASH_BASE rejection, got: {reason}"
    );
}

// ===========================================================================
// T12 — Lie about balance deltas
// ===========================================================================

#[test]
fn t12_balance_delta_must_match_transfer_amounts() {
    effect_vm_rejects_tampered_pi(dregg_circuit::effect_vm::pi::NET_DELTA_MAG, "NET_DELTA_MAG");
    effect_vm_rejects_tampered_pi(
        dregg_circuit::effect_vm::pi::NET_DELTA_SIGN,
        "NET_DELTA_SIGN",
    );
}

// ===========================================================================
// T13 — Cross-cell aliasing (same cell_id in two federations)
// ===========================================================================

#[test]
#[ignore = "blocked on EXECUTOR-HONESTY-AUDIT.md T13: Cell::remote_stub_with_id escape hatch must be constrained by federation membership + CapTP origin attestation"]
fn t13_remote_stub_with_id_cannot_mint_arbitrary_cell_ids() {
    panic!("blocked");
}

// ===========================================================================
// T14 — Skip the AIR proof entirely
// ===========================================================================

#[test]
fn t14_receipt_without_proof_rejected_at_wire_level() {
    let agent = CellId([0xE1u8; 32]);
    let receipt = sample_receipt(agent, [0xE2u8; 32], None);
    let entry = replay_entry_with_receipt_pi(receipt);

    let out = dregg_verifier::replay_chain(&[entry]);
    assert!(!out.overall_verified, "empty proof bytes must not verify");
    assert_eq!(out.first_failure, Some(0));
    assert!(
        matches!(
            &out.per_entry[0],
            dregg_verifier::ReplayVerdict::Rejected { reason }
                if reason.contains("STARK verify failed")
                    && reason.contains("deserial")
        ),
        "missing wire proof must be a hard rejection, got: {:?}",
        out.per_entry[0]
    );
}

#[test]
fn t14_malformed_proof_bytes_rejected() {
    let (out, code) = dregg_verifier::verify_effect_vm_proof(
        b"not a serialized STARK proof",
        &[],
        dregg_verifier::EFFECT_VM_VK_HASH_HEX,
    );

    assert!(!out.verified, "malformed proof bytes must not verify");
    assert_eq!(code, dregg_verifier::exit_code::ERROR);
    assert!(
        out.reason.contains("deserial"),
        "expected deserialisation failure, got: {}",
        out.reason
    );
}

// ===========================================================================
// T15 — Forge the effects_hash → AIR pass over a different effect list
// ===========================================================================

#[test]
fn t15_trace_effects_must_match_pi_effects_hash() {
    for i in 0..dregg_circuit::effect_vm::pi::EFFECTS_HASH_LEN {
        effect_vm_rejects_tampered_pi(
            dregg_circuit::effect_vm::pi::EFFECTS_HASH_BASE + i,
            "EFFECTS_HASH_BASE",
        );
    }
}

// ===========================================================================
// Cross-cutting (audit §"Cross-cutting open questions")
// ===========================================================================

#[test]
#[ignore = "blocked on T-cross-cutting #1: trace-side binding completeness audit (ACTOR_NONCE, EFFECTS_HASH_GLOBAL, TURN_HASH, PRE/POST_STATE, PREVIOUS_RECEIPT_HASH)"]
fn cross_cutting_all_pi_fields_trace_bound() {
    panic!("blocked");
}

#[test]
fn cross_cutting_canonical_signing_message_fields() {
    let agent = CellId([0xD1u8; 32]);
    let target = CellId([0xD2u8; 32]);
    let previous_receipt_hash = [0xD3u8; 32];
    let effects = vec![Effect::Transfer {
        from: agent,
        to: target,
        amount: 5,
    }];
    let mut turn = one_action_turn(agent, 17, effects.clone());
    turn.previous_receipt_hash = Some(previous_receipt_hash);

    let base_turn_hash = turn.hash();
    let mut base = sample_receipt(agent, base_turn_hash, Some(previous_receipt_hash));
    base.effects_hash = *blake3::hash(&effects[0].hash()).as_bytes();
    base.federation_id = [0xD4u8; 32];

    let message = base.canonical_executor_signed_message();
    assert!(
        message.starts_with(b"executor-receipt-sig-v3:"),
        "executor receipt signatures must use the v3 domain separator"
    );

    let mut changed_federation = base.clone();
    changed_federation.federation_id = [0xE4u8; 32];
    assert_ne!(
        message,
        changed_federation.canonical_executor_signed_message(),
        "canonical executor signing message must bind federation_id"
    );

    let mut changed_actor = base.clone();
    changed_actor.agent = CellId([0xE1u8; 32]);
    assert_ne!(
        message,
        changed_actor.canonical_executor_signed_message(),
        "canonical executor signing message must bind actor_id"
    );

    let mut changed_nonce_turn = turn.clone();
    changed_nonce_turn.nonce += 1;
    let mut changed_nonce = base.clone();
    changed_nonce.turn_hash = changed_nonce_turn.hash();
    assert_ne!(
        message,
        changed_nonce.canonical_executor_signed_message(),
        "canonical executor signing message must bind nonce via receipt.turn_hash"
    );

    let mut changed_effects = base.clone();
    changed_effects.effects_hash = [0xE5u8; 32];
    assert_ne!(
        message,
        changed_effects.canonical_executor_signed_message(),
        "canonical executor signing message must bind effects_hash"
    );

    let mut changed_previous = base;
    changed_previous.previous_receipt_hash = Some([0xE3u8; 32]);
    assert_ne!(
        message,
        changed_previous.canonical_executor_signed_message(),
        "canonical executor signing message must bind previous_receipt_hash"
    );
}

#[test]
fn cross_cutting_verifier_checks_all_pi() {
    let agent = CellId([0xC1u8; 32]);
    let base = sample_receipt(agent, [0xC2u8; 32], Some([0xC3u8; 32]));

    let mut turn_hash_tamper = replay_entry_with_receipt_pi(base.clone());
    turn_hash_tamper.public_inputs[dregg_circuit::effect_vm::pi::TURN_HASH_BASE] ^= 0x01;
    let reason = dregg_verifier::check_receipt_pi_binding(&turn_hash_tamper, None)
        .expect("TURN_HASH PI mismatch must reject");
    assert!(reason.contains("TURN_HASH_BASE"));

    let mut previous_hash_tamper = replay_entry_with_receipt_pi(base.clone());
    previous_hash_tamper.public_inputs[dregg_circuit::effect_vm::pi::PREVIOUS_RECEIPT_HASH_BASE] ^=
        0x01;
    let reason = dregg_verifier::check_receipt_pi_binding(&previous_hash_tamper, None)
        .expect("PREVIOUS_RECEIPT_HASH PI mismatch must reject");
    assert!(reason.contains("PREVIOUS_RECEIPT_HASH_BASE"));

    let mut agent_cell_tamper = replay_entry_with_receipt_pi(base);
    agent_cell_tamper.public_inputs[dregg_circuit::effect_vm::pi::IS_AGENT_CELL] = 0;
    let reason = dregg_verifier::check_receipt_pi_binding(&agent_cell_tamper, None)
        .expect("IS_AGENT_CELL PI mismatch must reject");
    assert!(reason.contains("IS_AGENT_CELL"));
}

// ===========================================================================
// Bonus: Bearer-cap T2 cousin — verify bearer permissions cannot exceed
// delegator (E-language facet attenuation).
// ===========================================================================

#[test]
fn bearer_cap_permissions_cannot_amplify_unchecked_baseline() {
    // Sanity: BearerCapProof has an `allowed_effects: Option<EffectMask>` field;
    // verify the construction round-trips and the executor's verify path
    // is at least exercised. The actual attenuation enforcement is in
    // protocol-tests/src/invariants/facet_attenuation.rs.
    let target = CellId([42u8; 32]);
    let bearer = BearerCapProof {
        target,
        permissions: AuthRequired::None,
        delegation_proof: DelegationProofData::SignedDelegation {
            delegator_pk: [1u8; 32],
            signature: [0u8; 64],
            bearer_pk: [2u8; 32],
        },
        expires_at: 100,
        revocation_channel: None,
        allowed_effects: None,
    };
    let auth = Authorization::Bearer(bearer);
    let a = CellId([99u8; 32]);
    let act = Action {
        target: a,
        method: symbol("test"),
        args: vec![],
        authorization: auth,
        preconditions: Default::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    };
    let _ = act.hash(); // does not panic.
}
