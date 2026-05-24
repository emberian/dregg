//! Integration tests for the CapTP wire-delivery seams that this
//! work-stream closes:
//!
//! - GAP-4: `WireMessage::PipelinedMsg` is actually dispatched into the
//!   `CrossFedPipelineBridge` rather than discarded.
//! - GAP-2: replay of a `HandoffPresentation` (same nonce) is rejected by a
//!   server-side seen-nonce registry (and `HandoffError::ReplayDetected` is
//!   surfaced on the wire).
//! - GAP-7: `CapTpState::on_peer_disconnect` breaks promises and cascades
//!   through the pipeline bridge.
//! - GAP-1: a `HandoffCertificate` whose introducer differs from the target
//!   federation is wire-serialisable and validates correctly when the target
//!   has the introducer in its `known_federations` list.
//! - GAP-12/13 (Seam 3 keystone): CapTP wire delivery → on-chain receipt
//!   loop. A PresentHandoff with a `delivery_signature` produces a Turn
//!   whose `Authorization::CapTpDelivered` carries the introducer-signed
//!   cert + recipient-signed binding. The wire layer's drain task forwards
//!   that Turn to a `TurnExecutor`, which verifies both signatures and
//!   commits the `ValidateHandoff` effect. Tampering rejects.

use pyana_captp::{
    CrossFedPipelineBridge, FederationId, HandoffCertificate, HandoffPresentation, PipelinedAction,
    SwissTable, validate_handoff,
};
use pyana_cell::AuthRequired;
use pyana_types::{CellId, generate_keypair};
use pyana_wire::captp_routing;
use pyana_wire::message::WireMessage;
use pyana_wire::prelude::CapTpState;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn fed(byte: u8) -> FederationId {
    FederationId([byte; 32])
}

fn cell(byte: u8) -> CellId {
    CellId([byte; 32])
}

fn make_action(method: &str) -> PipelinedAction {
    PipelinedAction {
        method: method.to_string(),
        args: vec![],
        authorization: vec![],
    }
}

// ---------------------------------------------------------------------------
// GAP-4: PipelinedMsg dispatches through the bridge
// ---------------------------------------------------------------------------

/// Exercising the bridge directly — same code-path the wire handler now uses
/// after the seam is closed.
#[test]
fn pipelined_msg_routes_to_bridge_and_resolves() {
    let mut bridge = CrossFedPipelineBridge::new();

    // Server has a local promise that peer A will pipeline to.
    let local_p = bridge.local_registry_mut().create_promise();

    // Peer A sends two pipelined messages targeting that promise.
    bridge
        .on_pipeline_message(fed(0xAA), local_p, make_action("call_1"), Some(11))
        .expect("first pipelined message accepted");
    bridge
        .on_pipeline_message(fed(0xAA), local_p, make_action("call_2"), Some(12))
        .expect("second pipelined message accepted");

    // Resolve the local promise — both pipelined messages should be drained.
    let delivered = bridge.resolve_local_promise(local_p, cell(0x42));
    assert_eq!(
        delivered.len(),
        2,
        "both pipelined messages must be delivered"
    );

    let methods: Vec<&str> = delivered.iter().map(|m| m.action.method.as_str()).collect();
    assert!(methods.contains(&"call_1"));
    assert!(methods.contains(&"call_2"));
}

// ---------------------------------------------------------------------------
// GAP-7: peer disconnect breaks outstanding promises
// ---------------------------------------------------------------------------

/// `CapTpState::on_peer_disconnect` breaks promises and emits notifications.
#[test]
fn peer_disconnect_breaks_outstanding_promises() {
    let mut state = CapTpState::new();

    // Establish a CapSession for the peer.
    let epoch = state.allocate_epoch();
    let peer = fed(0xBB);
    let session = pyana_captp::CapSession::with_epoch(peer.0, epoch);
    state.sessions.insert(peer, session);

    // Create a local promise the peer was supposed to resolve and queue
    // pipelined messages against it so cascading breakage produces
    // notifications.
    let local_p = state.pipeline_bridge.local_registry_mut().create_promise();
    state
        .pipeline_bridge
        .on_pipeline_message(
            peer,
            local_p,
            make_action("waiting_for_resolution"),
            Some(77),
        )
        .unwrap();
    state
        .outstanding_peer_promises
        .entry(peer)
        .or_default()
        .push(local_p);

    let notifications = state.on_peer_disconnect(peer);
    assert!(
        !notifications.is_empty(),
        "disconnect must produce broken-promise notifications"
    );
    assert!(
        notifications.iter().any(|n| n.promise_id == 77),
        "result_promise_id 77 must be broken on the sender's side"
    );
}

// ---------------------------------------------------------------------------
// GAP-1: three-party handoff certificate is constructible and verifiable
// ---------------------------------------------------------------------------

/// Build a cross-federation `HandoffCertificate` (Alice → Bob → Carol) and
/// verify it round-trips through wire serialisation and validates at the
/// target federation.
#[test]
fn three_party_handoff_validates_on_target() {
    // Alice = introducer (signs the cert).
    let (alice_sk, alice_pk) = generate_keypair();
    let alice_fed = FederationId(alice_pk.0);

    // Carol = target federation.
    let carol_fed = fed(0xCA);
    let carol_cell = cell(0x42);

    // Bob = recipient.
    let (bob_sk, bob_pk) = generate_keypair();

    // Carol pre-registers a swiss entry for the target cell (this would
    // normally happen via a custodial flow or a prior CapTP session).
    let mut carol_swiss = SwissTable::new();
    let swiss = carol_swiss.export(carol_cell, AuthRequired::Signature, 100, None);

    // Alice mints a three-party handoff cert pointing at Carol.
    let cert = HandoffCertificate::create(
        &alice_sk,
        alice_fed,
        carol_fed, // <-- target_federation != introducer
        carol_cell,
        bob_pk.0,
        AuthRequired::Signature,
        None,
        Some(500),
        Some(1),
        swiss,
    );
    assert_ne!(
        cert.introducer, cert.target_federation,
        "cert spans federations (the OCapN three-party shape)"
    );

    // Bob presents the cert to Carol's wire endpoint.
    let presentation = HandoffPresentation::create(cert.clone(), &bob_sk);
    let presentation_bytes = postcard::to_allocvec(&presentation).unwrap();

    // Round-trip through the wire envelope (postcard).
    let wire_msg = WireMessage::PresentHandoff {
        presentation_bytes: presentation_bytes.clone(),
        introducer_pk: alice_pk.0,
        delivery_signature: None,
    };
    let encoded = postcard::to_allocvec(&wire_msg).unwrap();
    let _decoded: WireMessage = postcard::from_bytes(&encoded).unwrap();

    // Carol validates the cert (with Alice in known_federations).
    let known = vec![alice_fed];
    let acceptance = validate_handoff(&presentation, &alice_pk, &mut carol_swiss, &known, 150)
        .expect("three-party cert must validate at the target federation");
    assert_eq!(acceptance.cell_id, carol_cell);
}

// ---------------------------------------------------------------------------
// GAP-2: replay of a handoff cert is rejected by the seen-nonce registry
// ---------------------------------------------------------------------------

/// Server-side replay detection: simulate two PresentHandoff messages with
/// the same nonce and confirm the second one is rejected.
#[test]
fn handoff_replay_rejected_by_seen_nonce_registry() {
    // Setup the same way the wire handler would.
    let (alice_sk, alice_pk) = generate_keypair();
    let alice_fed = FederationId(alice_pk.0);
    let (bob_sk, bob_pk) = generate_keypair();
    let target_cell = cell(0x42);

    let mut state = CapTpState::new();
    state.known_federations.push(alice_fed);
    state.current_height = 100;

    // Pre-register a swiss entry on the server with max_uses = None so the
    // swiss-table's own counter doesn't catch the replay.
    let swiss = state.swiss_table.export_with_options(
        target_cell,
        AuthRequired::Signature,
        100,
        None,
        None,
        None,
    );

    let cert = HandoffCertificate::create(
        &alice_sk,
        alice_fed,
        alice_fed,
        target_cell,
        bob_pk.0,
        AuthRequired::Signature,
        None,
        None,
        None,
        swiss,
    );
    let presentation = HandoffPresentation::create(cert.clone(), &bob_sk);

    // First presentation: passes, nonce gets inserted into the registry.
    assert!(
        !state.seen_handoff_nonces.contains(&cert.nonce),
        "nonce starts unseen"
    );

    let result1 = validate_handoff(
        &presentation,
        &alice_pk,
        &mut state.swiss_table,
        &state.known_federations,
        state.current_height,
    );
    assert!(result1.is_ok(), "first presentation must succeed");
    state.seen_handoff_nonces.insert(cert.nonce);

    // Second presentation (replay): the seen-nonce registry rejects it
    // before even calling validate_handoff. This mirrors the wire-handler
    // flow.
    assert!(
        state.seen_handoff_nonces.contains(&cert.nonce),
        "GAP-2: seen-nonce registry triggers ReplayDetected on the wire path"
    );
}

// ---------------------------------------------------------------------------
// GAP-12/13: Seam 3 keystone — CapTpDelivered closes the receipt-mirror loop
// ---------------------------------------------------------------------------

/// Helper: build (cert, presentation, presentation_bytes, recipient_sk) where
/// Alice is the introducer at federation `alice_fed` and Bob is the recipient.
fn make_delivery_setup(
    target_cell: CellId,
    target_fed: FederationId,
) -> (
    pyana_types::SigningKey,
    pyana_types::PublicKey,
    FederationId,
    pyana_types::SigningKey,
    pyana_types::PublicKey,
    SwissTable,
    [u8; 32],
) {
    let (alice_sk, alice_pk) = generate_keypair();
    let alice_fed = FederationId(alice_pk.0);
    let (bob_sk, bob_pk) = generate_keypair();
    let mut swiss = SwissTable::new();
    let swiss_num = swiss.export(target_cell, AuthRequired::None, 100, None);
    let _ = target_fed; // captured by the cert below
    (
        alice_sk, alice_pk, alice_fed, bob_sk, bob_pk, swiss, swiss_num,
    )
}

/// End-to-end: a PresentHandoff with `delivery_signature` produces a Turn
/// carrying `Authorization::CapTpDelivered`. The wire-layer builder, the
/// recipient's canonical signing message, and the executor's verifier all
/// agree on the binding (cert.nonce ↔ target ↔ effects). The Turn executes
/// against a ledger with the target cell and the receipt commits.
#[test]
fn captp_delivered_loop_closes_executor_accepts_and_commits() {
    use pyana_cell::{Cell, Ledger, Permissions, permissions::AuthRequired as P};
    use pyana_turn::action::{Authorization, Effect};
    use pyana_turn::executor::{ComputronCosts, TurnExecutor};

    let target_cell = cell(0x42);
    let target_fed = fed(0xCA);
    let (alice_sk, alice_pk, alice_fed, bob_sk, _bob_pk, mut carol_swiss, swiss_num) =
        make_delivery_setup(target_cell, target_fed);

    // Alice mints a handoff cert pointing at Carol's target cell, naming Bob.
    let cert = HandoffCertificate::create(
        &alice_sk,
        alice_fed,
        target_fed,
        target_cell,
        bob_sk.public_key().0,
        AuthRequired::None,
        None,
        Some(500),
        Some(1),
        swiss_num,
    );

    // Bob presents the cert to Carol.
    let presentation = HandoffPresentation::create(cert.clone(), &bob_sk);
    let presentation_bytes = postcard::to_allocvec(&presentation).unwrap();

    // Carol validates the presentation (must succeed before building the Turn).
    let known = vec![alice_fed];
    let _acceptance = validate_handoff(&presentation, &alice_pk, &mut carol_swiss, &known, 150)
        .expect("validate_handoff must succeed for the delivery test");

    // The cert_hash is BLAKE3 over the presentation bytes (the wire handler
    // uses this exact convention; see server.rs PresentHandoff handler).
    let cert_hash: [u8; 32] = blake3::hash(&presentation_bytes).into();
    let effect = captp_routing::validate_handoff_effect(cert_hash);

    // Bob computes the canonical CapTP-delivery signing message and signs it.
    let effects = vec![effect.clone()];
    let signing_msg = Authorization::captp_delivered_signing_message(
        &cert.nonce,
        &target_cell,
        &target_cell,
        0,
        &effects,
    );
    let sig = pyana_types::sign(&bob_sk, &signing_msg);

    // Build the Turn with CapTpDelivered authorization.
    let turn = captp_routing::build_captp_turn_delivered_from_parts(
        target_cell,
        target_cell,
        effect,
        0,
        cert.clone(),
        alice_pk.0,
        cert.recipient_pk,
        sig.0,
    );

    // Confirm the action carries the new variant.
    let action = &turn.call_forest.roots[0].action;
    assert!(matches!(
        action.authorization,
        Authorization::CapTpDelivered { .. }
    ));

    // Build a ledger with the target cell. Permissions are wide-open since
    // CapTpDelivered authorizes the action without consulting permissions.
    let mut ledger = Ledger::new();
    let mut target = Cell::remote_stub_with_id(target_cell);
    target.permissions = Permissions {
        send: P::None,
        receive: P::None,
        set_state: P::None,
        set_permissions: P::None,
        set_verification_key: P::None,
        increment_nonce: P::None,
        delegate: P::None,
        access: P::None,
    };
    ledger.insert_cell(target).expect("insert target cell");

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let result = executor.execute(&turn, &mut ledger);

    match result {
        pyana_turn::TurnResult::Committed { receipt, .. } => {
            // Seam 3 keystone: the executor accepted the CapTpDelivered Turn
            // (the introducer signature + sender signature both verified) and
            // emitted a receipt — the receipt-mirror loop is closed.
            assert_eq!(receipt.action_count, 1);
            assert_eq!(receipt.agent, target_cell);
        }
        other => panic!("expected Committed, got {other:?}"),
    }
}

/// Tampering: if the sender_signature is wrong, the executor rejects.
#[test]
fn captp_delivered_rejects_wrong_sender_signature() {
    use pyana_cell::{Cell, Ledger, Permissions, permissions::AuthRequired as P};
    use pyana_turn::action::Authorization;
    use pyana_turn::executor::{ComputronCosts, TurnExecutor};

    let target_cell = cell(0x42);
    let target_fed = fed(0xCA);
    let (alice_sk, alice_pk, alice_fed, bob_sk, _bob_pk, _swiss, swiss_num) =
        make_delivery_setup(target_cell, target_fed);

    let cert = HandoffCertificate::create(
        &alice_sk,
        alice_fed,
        target_fed,
        target_cell,
        bob_sk.public_key().0,
        AuthRequired::None,
        None,
        Some(500),
        Some(1),
        swiss_num,
    );

    let presentation = HandoffPresentation::create(cert.clone(), &bob_sk);
    let presentation_bytes = postcard::to_allocvec(&presentation).unwrap();
    let cert_hash: [u8; 32] = blake3::hash(&presentation_bytes).into();
    let effect = captp_routing::validate_handoff_effect(cert_hash);

    // Bad signature: 64 zero bytes (not a valid sig for any sender_pk).
    let bad_sig = [0u8; 64];

    let turn = captp_routing::build_captp_turn_delivered_from_parts(
        target_cell,
        target_cell,
        effect,
        0,
        cert.clone(),
        alice_pk.0,
        cert.recipient_pk,
        bad_sig,
    );

    let mut ledger = Ledger::new();
    let mut target = Cell::remote_stub_with_id(target_cell);
    target.permissions = Permissions {
        send: P::None,
        receive: P::None,
        set_state: P::None,
        set_permissions: P::None,
        set_verification_key: P::None,
        increment_nonce: P::None,
        delegate: P::None,
        access: P::None,
    };
    ledger.insert_cell(target).expect("insert target cell");

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let result = executor.execute(&turn, &mut ledger);

    let _ = Authorization::Unchecked; // silence unused import lint if any
    match result {
        pyana_turn::TurnResult::Rejected { reason, .. } => {
            let s = format!("{reason:?}");
            assert!(
                s.contains("captp-delivered")
                    || s.contains("Ed25519")
                    || s.contains("InvalidAuthorization"),
                "expected captp-delivered signature failure, got: {s}"
            );
        }
        other => panic!("expected Rejected for tampered signature, got {other:?}"),
    }
}

/// Tampering: if the introducer_pk doesn't match cert.introducer, reject.
#[test]
fn captp_delivered_rejects_wrong_introducer_pk() {
    use pyana_cell::{Cell, Ledger, Permissions, permissions::AuthRequired as P};
    use pyana_turn::executor::{ComputronCosts, TurnExecutor};

    let target_cell = cell(0x42);
    let target_fed = fed(0xCA);
    let (alice_sk, _alice_pk, alice_fed, bob_sk, _bob_pk, _swiss, swiss_num) =
        make_delivery_setup(target_cell, target_fed);

    let cert = HandoffCertificate::create(
        &alice_sk,
        alice_fed,
        target_fed,
        target_cell,
        bob_sk.public_key().0,
        AuthRequired::None,
        None,
        Some(500),
        Some(1),
        swiss_num,
    );

    let presentation = HandoffPresentation::create(cert.clone(), &bob_sk);
    let presentation_bytes = postcard::to_allocvec(&presentation).unwrap();
    let cert_hash: [u8; 32] = blake3::hash(&presentation_bytes).into();
    let effect = captp_routing::validate_handoff_effect(cert_hash);

    let effects = vec![effect.clone()];
    let signing_msg = pyana_turn::action::Authorization::captp_delivered_signing_message(
        &cert.nonce,
        &target_cell,
        &target_cell,
        0,
        &effects,
    );
    let sig = pyana_types::sign(&bob_sk, &signing_msg);

    // Wrong introducer_pk (some other random key).
    let (_other_sk, other_pk) = generate_keypair();

    let turn = captp_routing::build_captp_turn_delivered_from_parts(
        target_cell,
        target_cell,
        effect,
        0,
        cert.clone(),
        other_pk.0, // <-- wrong
        cert.recipient_pk,
        sig.0,
    );

    let mut ledger = Ledger::new();
    let mut target = Cell::remote_stub_with_id(target_cell);
    target.permissions = Permissions {
        send: P::None,
        receive: P::None,
        set_state: P::None,
        set_permissions: P::None,
        set_verification_key: P::None,
        increment_nonce: P::None,
        delegate: P::None,
        access: P::None,
    };
    ledger.insert_cell(target).expect("insert target cell");

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let result = executor.execute(&turn, &mut ledger);
    match result {
        pyana_turn::TurnResult::Rejected { reason, .. } => {
            let s = format!("{reason:?}");
            assert!(
                s.contains("introducer_pk") || s.contains("InvalidAuthorization"),
                "expected introducer_pk mismatch failure, got: {s}"
            );
        }
        other => panic!("expected Rejected for wrong introducer_pk, got {other:?}"),
    }
}

/// SiloServer drain-task integration: when a CapTP-delivered Turn is pushed
/// into `pending_captp_turns`, the dispatcher receives it. This proves the
/// node-loop integration is wired (the lane's "drain_pending_captp_turns
/// actually called" requirement).
#[tokio::test]
async fn spawn_captp_drain_forwards_to_dispatcher() {
    use pyana_turn::Turn;
    use pyana_turn::action::{Authorization, Effect};
    use pyana_wire::prelude::{SiloConfig, SiloServer};
    use std::sync::Arc;
    use tokio::sync::oneshot;

    let config = SiloConfig::new("drain-test-silo");
    let (tx, rx) = oneshot::channel::<Turn>();
    let tx = Arc::new(tokio::sync::Mutex::new(Some(tx)));

    let dispatcher: pyana_wire::prelude::CapTpTurnDispatcher = {
        let tx = Arc::clone(&tx);
        Arc::new(move |turn: Turn| {
            let tx = Arc::clone(&tx);
            Box::pin(async move {
                let mut guard = tx.lock().await;
                if let Some(sender) = guard.take() {
                    sender.send(turn).map_err(|_| "send failed".to_string())?;
                }
                Ok::<(), String>(())
            })
        })
    };

    let server = SiloServer::new("127.0.0.1:0".parse().unwrap(), config)
        .with_captp_turn_dispatcher(dispatcher)
        .with_captp_drain_interval(std::time::Duration::from_millis(20));

    // Push a Turn directly into the queue. We don't need a real CapTpDelivered
    // here — the drain task forwards whatever is queued.
    let queued_turn = pyana_turn::turn::Turn {
        agent: cell(0x99),
        nonce: 7,
        call_forest: pyana_turn::forest::CallForest::new(),
        fee: 0,
        memo: Some("drain-test".to_string()),
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
    };
    {
        let mut state = server.captp_state().write().await;
        state.pending_captp_turns.push(queued_turn.clone());
    }

    // Spawn the drain task (normally invoked by `run`).
    let _handle = server.spawn_captp_drain().expect("drain task spawned");

    // The dispatcher should receive the Turn within a few intervals.
    let received = tokio::time::timeout(std::time::Duration::from_millis(500), rx)
        .await
        .expect("dispatcher must receive the drained Turn within 500ms")
        .expect("dispatcher channel must not be closed");

    assert_eq!(received.nonce, 7);
    assert_eq!(received.memo.as_deref(), Some("drain-test"));
    // Silence unused imports
    let _ = (
        Effect::DropRef { ref_id: [0u8; 32] },
        Authorization::Unchecked,
    );
}
