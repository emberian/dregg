//! Silver E2E: CapTP-delivered turn evidence across federations.
//!
//! This is deliberately in-process rather than socket-based. The test uses the
//! real CapTP handoff validator, the real `Authorization::CapTpDelivered`
//! executor path, real `TurnReceipt`s, real Effect-VM proofs for replay, and the
//! cross-federation bundle verifier. The remaining live-wire gap is transport:
//! a production cclerk still has to route this same handoff/turn material over
//! the network.

use std::collections::HashMap;

use dregg_captp::{
    FederationId as CapTpFederationId, HandoffCertificate, HandoffPresentation, SwissTable,
    validate_handoff,
};
use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::{
    BabyBear, CellState, Effect as VmEffect, EffectVmAir,
    effect_vm::{generate_effect_vm_trace, pi},
    stark::{self, proof_to_bytes},
};
use dregg_commit::typed::canonical_32_to_felts_4;
use dregg_federation::{CrossFedReceiptBundle, derive_federation_id_with_epoch};
use dregg_teasting::harness::SimulationHarness;
use dregg_turn::{
    ActionBuilder, Authorization, CallForest, CommitmentMode, ComputronCosts, DelegationMode,
    Effect, Turn, TurnExecutor, TurnResult, WitnessedReceipt,
};
use dregg_types::{
    AttestedRoot, CellId, PublicKey, SigningKey, merkle_root_of_receipt_hashes, sign,
};
use dregg_verifier::cross_fed::{
    CommitteeDescriptor, ValidatorDescriptor, verify_cross_fed_bundle,
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

fn token_id() -> [u8; 32] {
    *blake3::hash(b"silver-captp-turn-token").as_bytes()
}

fn cell(seed: &str, balance: u64) -> Cell {
    let key_bytes = *blake3::hash(format!("silver-captp-cell:{seed}").as_bytes()).as_bytes();
    let mut cell = Cell::with_balance(key_bytes, token_id(), balance);
    cell.permissions = open_permissions();
    cell
}

fn hex_32(bytes: &[u8; 32]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn committee_descriptor(harness: &SimulationHarness, fed_idx: usize) -> CommitteeDescriptor {
    let fed = &harness.federations[fed_idx].canonical;
    let validators = fed
        .members()
        .iter()
        .enumerate()
        .map(|(i, pk)| ValidatorDescriptor {
            name: format!("f{fed_idx}-validator-{i}"),
            public_key: hex_32(&pk.0),
        })
        .collect();
    CommitteeDescriptor {
        federation_id: hex_32(&fed.id_bytes()),
        committee_epoch: fed.epoch(),
        threshold: fed.threshold_usize(),
        validators,
    }
}

fn sign_attested_root(mut root: AttestedRoot, signing_key: &SigningKey) -> AttestedRoot {
    let pk = signing_key.public_key();
    let sig = sign(signing_key, &root.signing_message());
    root.quorum_signatures = vec![(pk, sig)];
    root
}

fn attested_root_for_receipts(
    federation_id: [u8; 32],
    receipt_hashes: &[[u8; 32]],
    signing_key: &SigningKey,
    height: u64,
    tag: &[u8],
) -> AttestedRoot {
    let receipt_stream_root = merkle_root_of_receipt_hashes(receipt_hashes);
    let mut h = blake3::Hasher::new_derive_key("dregg-teasting-silver-captp-root-v1");
    h.update(tag);
    h.update(&height.to_le_bytes());
    h.update(&receipt_stream_root);
    let merkle_root = *h.finalize().as_bytes();
    sign_attested_root(
        AttestedRoot {
            merkle_root,
            note_tree_root: None,
            nullifier_set_root: None,
            height,
            timestamp: 1_700_000_000 + height as i64,
            blocklace_block_id: Some(
                *blake3::hash([tag, b":blocklace"].concat().as_slice()).as_bytes(),
            ),
            finality_round: Some(height),
            quorum_signatures: Vec::new(),
            threshold_qc: None,
            threshold: 1,
            federation_id: dregg_types::FederationId(federation_id),
            receipt_stream_root: Some(receipt_stream_root),
        },
        signing_key,
    )
}

fn build_turn(
    agent: CellId,
    nonce: u64,
    previous_receipt_hash: Option<[u8; 32]>,
    action: dregg_turn::Action,
) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(action);
    Turn {
        agent,
        nonce,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash,
        depends_on: Vec::new(),
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

fn execute_or_panic(
    executor: &TurnExecutor,
    ledger: &mut Ledger,
    turn: &Turn,
    label: &str,
) -> dregg_turn::TurnReceipt {
    match executor.execute(turn, ledger) {
        TurnResult::Committed { receipt, .. } => receipt,
        TurnResult::Rejected { reason, at_action } => {
            panic!("{label} rejected at {at_action:?}: {reason}");
        }
        other => panic!("{label} did not commit: {other:?}"),
    }
}

fn build_witnessed_receipt(receipt: dregg_turn::TurnReceipt, balance: u64) -> WitnessedReceipt {
    let state = CellState::new(balance, 0);
    let vm_effects = [VmEffect::SetField {
        field_idx: 0,
        value: BabyBear::new(7),
    }];
    let (trace, mut public_inputs) = generate_effect_vm_trace(&state, &vm_effects);
    let needed = pi::BASE_COUNT
        .max(pi::TURN_HASH_BASE + pi::TURN_HASH_LEN)
        .max(pi::PREVIOUS_RECEIPT_HASH_BASE + pi::PREVIOUS_RECEIPT_HASH_LEN);
    if public_inputs.len() < needed {
        public_inputs.resize(needed, BabyBear::ZERO);
    }

    let turn_hash = canonical_32_to_felts_4(&receipt.turn_hash);
    for i in 0..pi::TURN_HASH_LEN {
        public_inputs[pi::TURN_HASH_BASE + i] = turn_hash[i];
    }
    let previous = canonical_32_to_felts_4(&receipt.previous_receipt_hash.unwrap_or([0u8; 32]));
    for i in 0..pi::PREVIOUS_RECEIPT_HASH_LEN {
        public_inputs[pi::PREVIOUS_RECEIPT_HASH_BASE + i] = previous[i];
    }
    if public_inputs.len() > pi::IS_AGENT_CELL {
        public_inputs[pi::IS_AGENT_CELL] = BabyBear::ONE;
    }

    let air = EffectVmAir::new(trace.len());
    let proof = stark::prove(&air, &trace, &public_inputs);
    let proof_bytes = proof_to_bytes(&proof);
    WitnessedReceipt::from_components(
        receipt,
        proof_bytes,
        public_inputs.iter().map(|b| b.as_u32()).collect(),
        Some(&trace),
    )
}

struct SilverScenario {
    issuer_desc: CommitteeDescriptor,
    recipient_desc: CommitteeDescriptor,
    bundle: CrossFedReceiptBundle,
    f2_exercise_turn: Turn,
    f2_exercise_receipt: dregg_turn::TurnReceipt,
    f2_executor: TurnExecutor,
    f2_ledger: Ledger,
    cert: HandoffCertificate,
    bob_sk: SigningKey,
    f1_pk: PublicKey,
    f2_fed_id: [u8; 32],
    gateway_id: CellId,
}

fn build_silver_scenario() -> SilverScenario {
    let harness = SimulationHarness::two_federations(1, 1);
    let f1_sk = harness.federations[0].all_signing_keys_canonical_order()[0].clone();
    let f2_sk = harness.federations[1].all_signing_keys_canonical_order()[0].clone();
    let f1_pk = f1_sk.public_key();
    let f1_fed_id = harness.federations[0].canonical.id_bytes();
    let f2_fed_id = harness.federations[1].canonical.id_bytes();
    assert_eq!(
        f1_fed_id,
        derive_federation_id_with_epoch(&[f1_pk], 0),
        "single-node descriptor id must derive from its validator key",
    );

    let (bob_sk, bob_pk) = dregg_types::generate_keypair();
    let f1_issuer = cell("f1-issuer", 1_000_000);
    let gateway = cell("f2-gateway", 1_000_000);
    let gateway_id = gateway.id();

    let mut f1_ledger = Ledger::new();
    let f1_issuer_id = f1_issuer.id();
    f1_ledger.insert_cell(f1_issuer).unwrap();
    let mut f1_executor = TurnExecutor::new(ComputronCosts::zero());
    f1_executor.set_local_federation_id(f1_fed_id);
    f1_executor.set_executor_signing_key(f1_sk.to_bytes());

    let swiss = *blake3::hash(b"silver-captp-swiss").as_bytes();
    let issue_effect = Effect::ExportSturdyRef {
        swiss_number: swiss,
        target: f1_issuer_id,
        permissions: AuthRequired::None,
    };
    let issue_action = ActionBuilder::new_unchecked_for_tests(
        f1_issuer_id,
        "export_for_captp_handoff",
        f1_issuer_id,
    )
    .delegation(DelegationMode::None)
    .commitment_mode(CommitmentMode::Full)
    .effect(issue_effect)
    .build();
    let f1_issue_turn = build_turn(f1_issuer_id, 0, None, issue_action);
    let f1_issue_receipt =
        execute_or_panic(&f1_executor, &mut f1_ledger, &f1_issue_turn, "F1 issue");

    let mut swiss_table = SwissTable::new();
    let registered_swiss = swiss_table.export(gateway_id, AuthRequired::None, 0, None);
    let cert = HandoffCertificate::create(
        &f1_sk,
        CapTpFederationId(f1_fed_id),
        CapTpFederationId(f2_fed_id),
        gateway_id,
        bob_pk.0,
        AuthRequired::None,
        Some(dregg_cell::EFFECT_SET_FIELD | dregg_cell::EFFECT_CAPTP_OPS),
        Some(100),
        Some(1),
        registered_swiss,
    );
    let presentation = HandoffPresentation::create(cert.clone(), &bob_sk);
    let acceptance = validate_handoff(
        &presentation,
        &f1_pk,
        &mut swiss_table,
        &[CapTpFederationId(f1_fed_id)],
        1,
    )
    .expect("F2 must validate F1 handoff before constructing the turn");
    assert_eq!(acceptance.cell_id, gateway_id);
    assert_eq!(acceptance.permissions, AuthRequired::None);

    let mut f2_ledger = Ledger::new();
    f2_ledger.insert_cell(gateway).unwrap();
    let mut f2_executor = TurnExecutor::new(ComputronCosts::zero());
    f2_executor.set_local_federation_id(f2_fed_id);
    f2_executor.set_executor_signing_key(f2_sk.to_bytes());

    let prep_action =
        ActionBuilder::new_unchecked_for_tests(gateway_id, "prepare_receiver", gateway_id)
            .effect(Effect::SetField {
                cell: gateway_id,
                index: 0,
                value: *blake3::hash(b"receiver-ready").as_bytes(),
            })
            .build();
    let prep_turn = build_turn(gateway_id, 0, None, prep_action);
    let prep_receipt = execute_or_panic(&f2_executor, &mut f2_ledger, &prep_turn, "F2 prep");

    let captp_effects = vec![
        Effect::ValidateHandoff {
            cert_hash: *blake3::hash(&cert.to_bytes()).as_bytes(),
            recipient_pk: bob_pk.0,
            introducer_pk: f1_pk.0,
        },
        Effect::SetField {
            cell: gateway_id,
            index: 1,
            value: *blake3::hash(b"captp-delivered-turn-accepted").as_bytes(),
        },
    ];
    let sender_message = Authorization::captp_delivered_signing_message_for_federation(
        &f2_fed_id,
        &cert.nonce,
        &gateway_id,
        &gateway_id,
        1,
        &captp_effects,
    );
    let sender_signature = sign(&bob_sk, &sender_message).0;
    let mut captp_action =
        ActionBuilder::new_unchecked_for_tests(gateway_id, "captp_delivered_exercise", gateway_id)
            .delegation(DelegationMode::None)
            .commitment_mode(CommitmentMode::Full)
            .build();
    captp_action.authorization = Authorization::CapTpDelivered {
        handoff_cert: cert.clone(),
        introducer_pk: f1_pk.0,
        sender_pk: bob_pk.0,
        sender_signature,
    };
    captp_action.effects = captp_effects;
    let f2_exercise_turn = build_turn(
        gateway_id,
        1,
        Some(prep_receipt.receipt_hash()),
        captp_action,
    );
    let f2_exercise_receipt = execute_or_panic(
        &f2_executor,
        &mut f2_ledger,
        &f2_exercise_turn,
        "F2 CapTP exercise",
    );
    assert_eq!(
        f2_ledger.get(&gateway_id).unwrap().state.fields[1],
        *blake3::hash(b"captp-delivered-turn-accepted").as_bytes(),
    );

    let f1_hashes = [f1_issue_receipt.receipt_hash()];
    let f2_hashes = [
        prep_receipt.receipt_hash(),
        f2_exercise_receipt.receipt_hash(),
    ];
    let f1_root = attested_root_for_receipts(f1_fed_id, &f1_hashes, &f1_sk, 10, b"f1");
    let f2_root = attested_root_for_receipts(f2_fed_id, &f2_hashes, &f2_sk, 20, b"f2");

    let recipient_chain = vec![
        build_witnessed_receipt(prep_receipt.clone(), 10_000),
        build_witnessed_receipt(f2_exercise_receipt.clone(), 10_100),
    ];
    let recipient_federation_receipt = Some(harness.lift_turn_receipt(
        1,
        &f2_exercise_receipt,
        f2_exercise_turn.nonce,
        20,
        *blake3::hash(b"f2-captp-exercise-block").as_bytes(),
    ));

    let issuer_desc = committee_descriptor(&harness, 0);
    let recipient_desc = committee_descriptor(&harness, 1);
    let bundle = CrossFedReceiptBundle::new(
        recipient_chain,
        f1_root,
        f2_root,
        cert.clone(),
        recipient_federation_receipt,
    );

    SilverScenario {
        issuer_desc,
        recipient_desc,
        bundle,
        f2_exercise_turn,
        f2_exercise_receipt,
        f2_executor,
        f2_ledger,
        cert,
        bob_sk,
        f1_pk,
        f2_fed_id,
        gateway_id,
    }
}

fn assert_bundle_rejects(
    bundle: &CrossFedReceiptBundle,
    issuer_desc: &CommitteeDescriptor,
    recipient_desc: &CommitteeDescriptor,
    expected: &str,
) {
    let verdict = verify_cross_fed_bundle(bundle, issuer_desc, recipient_desc);
    assert!(
        !verdict.overall_verified,
        "tampered bundle unexpectedly verified: {verdict:?}",
    );
    assert!(
        verdict.summary.contains(expected),
        "expected rejection containing {expected:?}, got {:?}",
        verdict.summary,
    );
}

#[test]
fn silver_captp_delivered_turn_verifies_across_federations() {
    let scenario = build_silver_scenario();
    let verdict = verify_cross_fed_bundle(
        &scenario.bundle,
        &scenario.issuer_desc,
        &scenario.recipient_desc,
    );
    assert!(
        verdict.overall_verified,
        "Silver CapTP bundle must verify end-to-end: {verdict:?}",
    );
    assert!(verdict.cert_introducer_sig_verified);
    assert!(verdict.effect_vm_proof_verified);
    assert!(verdict.witness_chain_replay_verified);
    assert!(verdict.attested_root_f2_blocklace_bound);
    assert!(verdict.executor_signature_includes_federation_id);
}

#[test]
fn silver_captp_adversarial_bundle_mutations_reject() {
    let scenario = build_silver_scenario();

    let mut swapped_recipient = scenario.bundle.clone();
    swapped_recipient.cross_fed_cert.target_federation = CapTpFederationId([0xF2; 32]);
    assert_bundle_rejects(
        &swapped_recipient,
        &scenario.issuer_desc,
        &scenario.recipient_desc,
        "cert introducer signature did not verify",
    );

    let mut swapped_federation = scenario.bundle.clone();
    swapped_federation.recipient_chain[1].receipt.federation_id = [0xEE; 32];
    assert_bundle_rejects(
        &swapped_federation,
        &scenario.issuer_desc,
        &scenario.recipient_desc,
        "F2 AttestedRoot receipt_stream_root does not match recipient_chain receipts",
    );

    let mut missing_witness = scenario.bundle.clone();
    missing_witness.recipient_chain[1].witness_bundle = None;
    assert_bundle_rejects(
        &missing_witness,
        &scenario.issuer_desc,
        &scenario.recipient_desc,
        "has no witness_bundle",
    );

    let mut broken_previous = scenario.bundle.clone();
    broken_previous.recipient_chain[1]
        .receipt
        .previous_receipt_hash = Some([0xAB; 32]);
    assert_bundle_rejects(
        &broken_previous,
        &scenario.issuer_desc,
        &scenario.recipient_desc,
        "scope-2 replay failed",
    );
}

#[test]
fn captp_delivered_executor_rejects_wrong_target_or_federation() {
    let scenario = build_silver_scenario();
    let original_action = scenario
        .f2_exercise_turn
        .call_forest
        .roots
        .first()
        .expect("exercise turn has a root")
        .action
        .clone();

    let mut wrong_target_action = original_action.clone();
    let mut wrong_target_cert = scenario.cert.clone();
    wrong_target_cert.target_cell = CellId([0x44; 32]);
    if let Authorization::CapTpDelivered { handoff_cert, .. } =
        &mut wrong_target_action.authorization
    {
        *handoff_cert = wrong_target_cert;
    }
    let wrong_target_turn = build_turn(
        scenario.gateway_id,
        2,
        Some(scenario.f2_exercise_receipt.receipt_hash()),
        wrong_target_action,
    );
    assert!(matches!(
        scenario
            .f2_executor
            .execute(&wrong_target_turn, &mut scenario.f2_ledger.clone()),
        TurnResult::Rejected { reason, .. }
            if reason.to_string().contains("cert.target_cell does not match action target")
    ));

    let mut wrong_federation_action = original_action;
    let mut wrong_federation_cert = scenario.cert;
    wrong_federation_cert.target_federation = CapTpFederationId([0x55; 32]);
    if let Authorization::CapTpDelivered { handoff_cert, .. } =
        &mut wrong_federation_action.authorization
    {
        *handoff_cert = wrong_federation_cert;
    }
    let wrong_federation_turn = build_turn(
        scenario.gateway_id,
        2,
        Some(scenario.f2_exercise_receipt.receipt_hash()),
        wrong_federation_action,
    );
    assert_ne!(scenario.f2_fed_id, [0x55; 32]);
    assert!(matches!(
        scenario
            .f2_executor
            .execute(&wrong_federation_turn, &mut scenario.f2_ledger.clone()),
        TurnResult::Rejected { reason, .. }
            if reason.to_string().contains("cert.target_federation does not match local federation")
    ));
}

#[test]
fn captp_delivered_executor_rejects_swapped_recipient_signature() {
    let scenario = build_silver_scenario();
    let mut action = scenario
        .f2_exercise_turn
        .call_forest
        .roots
        .first()
        .expect("exercise turn has a root")
        .action
        .clone();
    let (_, impostor_pk) = dregg_types::generate_keypair();
    if let Authorization::CapTpDelivered { sender_pk, .. } = &mut action.authorization {
        *sender_pk = impostor_pk.0;
    }
    let turn = build_turn(
        scenario.gateway_id,
        2,
        Some(scenario.f2_exercise_receipt.receipt_hash()),
        action,
    );
    assert!(matches!(
        scenario.f2_executor.execute(&turn, &mut scenario.f2_ledger.clone()),
        TurnResult::Rejected { reason, .. }
            if reason.to_string().contains("sender_pk does not match cert.recipient_pk")
    ));

    let presentation = HandoffPresentation::create(scenario.cert, &scenario.bob_sk);
    let mut empty_table = SwissTable::new();
    assert!(
        validate_handoff(
            &presentation,
            &scenario.f1_pk,
            &mut empty_table,
            &[CapTpFederationId(scenario.f2_fed_id)],
            1,
        )
        .is_err(),
        "missing target-side handoff/swiss witness must reject before turn construction",
    );
}
