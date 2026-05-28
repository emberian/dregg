//! Cross-app composition e2e — the multi-app gate that was missing.
//!
//! Every starbridge-app has its own executor-invoking integration test, but
//! nothing composed *multiple* apps into one causal flow. This drives THREE
//! apps — identity, nameservice, subscription — through a single shared
//! `EmbeddedExecutor` (one ledger, one agent cipherclerk, three app cells)
//! and asserts two Silver-Vision integration properties the per-app tests
//! cannot:
//!
//!   1. all the apps' turns compose into ONE causal receipt chain — each
//!      receipt links to the previous (`previous_receipt_hash`) across every
//!      app boundary; and
//!   2. re-executing the *same* turns reproduces identical state transitions
//!      (`turn_hash`, pre/post state roots, `effects_hash`) — replay
//!      determinism of derivable state. (The `receipt_hash`/`timestamp`
//!      legitimately differ run-to-run because the executor stamps wall-clock
//!      time; replay determinism is a property of the state, not the clock.)
//!
//! Flow (one agent; identity cell + nameservice cell + subscription cell in
//! one ledger; the agent holds a capability to each non-primary cell — dregg
//! is a capability mesh, so cross-cell action is gated on an explicit
//! capability, not mere co-ownership):
//!   identity:     issue a KYC credential → present it → verify it (accept)
//!   nameservice:  register a name
//!   subscription: grant publisher → publish → grant consumer → consume
//!
//! NOTE: the *credential-gated* nameservice tier
//! (`build_register_with_credential_action`) is intentionally NOT used: its
//! BlindedSet WitnessedPredicate verifier is fail-closed (NotYetWired) in the
//! embedded executor (tracked separately), so that accept path cannot
//! complete end-to-end. This uses the achievable accept paths so the gate is
//! real, not theater.

use dregg_app_framework::{AgentCipherclerk, AppCipherclerk, CellId, EmbeddedExecutor};
use dregg_cell::permissions::AuthRequired;
use dregg_cell::program::{CellProgram, TransitionCase, TransitionGuard};
use dregg_cell::{Cell, StateConstraint};
use dregg_turn::{Action, TurnReceipt};

use starbridge_identity::{
    AttrValue, CredentialAttributes, IssuerKeys, Predicate, PredicateRequest, PresentationOptions,
    REVOCATION_ROOT_SLOT, VerificationOptions, build_issue_credential_action,
    build_present_credential_action, build_verify_presentation_action, issue, kyc_schema, present,
};
use starbridge_nameservice::{build_register_action, name_cell_program};
use starbridge_subscription::{
    build_consume_action, build_grant_consumer_action, build_grant_publisher_action,
    build_publish_action, subscription_program,
};

fn agent(seed: u8) -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::from_seed([seed; 64]), [42u8; 32])
}

fn blake3_field(bytes: &[u8]) -> [u8; 32] {
    *blake3::hash(bytes).as_bytes()
}

fn u64_field(value: u64) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[24..32].copy_from_slice(&value.to_be_bytes());
    out
}

fn issuer_keys() -> IssuerKeys {
    IssuerKeys::new(
        [100u8; 32],
        [
            3, 154, 242, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0,
        ],
        b"composition-test",
        "starbridge-identity",
    )
}

fn attributes() -> CredentialAttributes {
    CredentialAttributes::new()
        .with("given_name", AttrValue::Text("Alice".into()))
        .with("verification_level", AttrValue::Integer(2))
}

/// Strip `SenderAuthorized` constraints so the embedded executor (no
/// credential-set verifier wired) reaches effect application — the
/// established idiom in the per-app integration tests.
fn shape(program: CellProgram) -> CellProgram {
    let strip = |ks: Vec<StateConstraint>| {
        ks.into_iter()
            .filter(|k| !matches!(k, StateConstraint::SenderAuthorized { .. }))
            .collect::<Vec<_>>()
    };
    match program {
        CellProgram::Cases(cases) => CellProgram::Cases(
            cases
                .into_iter()
                .map(|mut c| {
                    c.constraints = strip(std::mem::take(&mut c.constraints));
                    c
                })
                .collect(),
        ),
        CellProgram::Predicate(ks) => CellProgram::Cases(vec![TransitionCase {
            guard: TransitionGuard::Always,
            constraints: strip(ks),
        }]),
        other => other,
    }
}

/// A fully-set-up shared-ledger environment: one agent and three app cells,
/// with the agent granted a capability to reach each non-primary cell.
struct Env {
    executor: EmbeddedExecutor,
    cipherclerk: AppCipherclerk,
    identity_cell: CellId,
    ns_cell: CellId,
    sub_cell: CellId,
    owner_pk: [u8; 32],
}

fn fresh_env(seed: u8) -> Env {
    let cipherclerk = agent(seed);
    let executor = EmbeddedExecutor::new(&cipherclerk, "default");
    let owner_pk = cipherclerk.public_key().0;

    // identity cell = the agent's primary cell; enforce revocation-root
    // monotonicity (a real identity caveat).
    let identity_cell = executor.cell_id();
    executor.install_program(
        identity_cell,
        CellProgram::Predicate(vec![StateConstraint::Monotonic {
            index: REVOCATION_ROOT_SLOT as u8,
        }]),
    );

    // nameservice + subscription cells, owned by the same agent.
    let mk_cell = |domain: &[u8]| Cell::with_balance(owner_pk, *blake3::hash(domain).as_bytes(), 1_000_000);
    let ns_obj = mk_cell(b"nameservice");
    let ns_cell = ns_obj.id();
    executor.ensure_cell(ns_obj).expect("ns cell inserts");
    executor.install_program(ns_cell, shape(name_cell_program()));

    let sub_obj = mk_cell(b"subscription");
    let sub_cell = sub_obj.id();
    executor.ensure_cell(sub_obj).expect("subscription cell inserts");
    executor.install_program(sub_cell, shape(subscription_program()));

    // Grant the primary cell capabilities to reach the two app cells.
    executor.with_ledger_mut(|ledger| {
        if let Some(agent_cell) = ledger.get_mut(&identity_cell) {
            agent_cell.capabilities.grant(ns_cell, AuthRequired::None);
            agent_cell.capabilities.grant(sub_cell, AuthRequired::None);
        }
    });

    Env { executor, cipherclerk, identity_cell, ns_cell, sub_cell, owner_pk }
}

/// Build the ordered composition actions. Randomness in credential issuance /
/// presentation is captured *once* here, so the returned actions replay
/// deterministically when re-submitted.
fn build_actions(env: &Env) -> Vec<Action> {
    let cc = &env.cipherclerk;

    // ── identity: issue → present → verify ──────────────────────────────
    let schema = kyc_schema();
    let credential = issue(&issuer_keys(), &schema, [9u8; 32], attributes(), 1_700_000_000, None)
        .expect("issuance succeeds");
    let issue_action = build_issue_credential_action(cc, env.identity_cell, &credential, 1, [0u8; 32]);

    let opts = PresentationOptions::new()
        .disclose("verification_level")
        .predicate(PredicateRequest::new("verification_level", Predicate::Gte(1)));
    let presentation = present(
        &credential,
        &dregg_token::AuthRequest {
            action: Some("read".into()),
            app_id: Some("composition-test".into()),
            user_id: Some("0909090909090909090909090909090909090909090909090909090909090909".into()),
            now: Some(1_700_000_000),
            ..Default::default()
        },
        &opts,
    )
    .expect("presentation builds");
    let present_action = build_present_credential_action(cc, env.identity_cell, &presentation);

    let verify_opts = VerificationOptions {
        expected_schema: Some(schema),
        expected_disclosure: vec!["verification_level".into()],
        expected_predicates: vec![PredicateRequest::new("verification_level", Predicate::Gte(1))],
        ..Default::default()
    };
    let verify_action =
        build_verify_presentation_action(cc, env.identity_cell, &presentation, &verify_opts);

    // ── nameservice: register ───────────────────────────────────────────
    let register_action =
        build_register_action(cc, env.ns_cell, "alice.dregg", env.owner_pk, 10_000);

    // ── subscription: grant publisher → publish → grant consumer → consume ─
    let payload = blake3_field(b"composition-payload");
    let grant_pub = build_grant_publisher_action(
        cc,
        env.sub_cell,
        blake3_field(b"publishers-root-v1"),
        [0x11u8; 32],
    );
    let publish = build_publish_action(
        cc,
        env.sub_cell,
        u64_field(1),
        blake3_field(b"message-root-v1"),
        payload,
    );
    let grant_con = build_grant_consumer_action(
        cc,
        env.sub_cell,
        blake3_field(b"consumers-root-v1"),
        [0x22u8; 32],
    );
    let consume = build_consume_action(cc, env.sub_cell, u64_field(1), payload);

    vec![
        issue_action,
        present_action,
        verify_action,
        register_action,
        grant_pub,
        publish,
        grant_con,
        consume,
    ]
}

fn submit_all(env: &Env, actions: &[Action]) -> Vec<TurnReceipt> {
    actions
        .iter()
        .map(|a| {
            env.executor
                .submit_action(&env.cipherclerk, a.clone())
                .expect("composition action commits")
        })
        .collect()
}

#[test]
fn cross_app_composition_chains_one_receipt_chain_and_emits_events() {
    let env = fresh_env(7);
    let actions = build_actions(&env);
    let receipts = submit_all(&env, &actions);
    assert_eq!(
        receipts.len(),
        8,
        "issue, present, verify, register, grant_pub, publish, grant_con, consume"
    );

    for (i, r) in receipts.iter().enumerate() {
        assert!(!r.emitted_events.is_empty(), "turn {i} must emit an event");
        assert_eq!(r.action_count, 1, "each composition turn carries one action");
    }

    // identity verify (turn 2) accepted the presentation.
    assert_eq!(
        receipts[2].emitted_events[0].data[1][31], 1,
        "presentation must verify as accepted"
    );

    // THE composition property: all eight turns — across identity,
    // nameservice, and subscription — form ONE causal receipt chain.
    assert_eq!(receipts[0].previous_receipt_hash, None, "first turn is genesis");
    for i in 1..receipts.len() {
        assert_eq!(
            receipts[i].previous_receipt_hash,
            Some(receipts[i - 1].receipt_hash()),
            "turn {i} must link to turn {}'s receipt across the app boundary",
            i - 1
        );
    }
}

#[test]
fn cross_app_composition_state_transitions_are_deterministic_on_replay() {
    // Build the actions once (credential/presentation randomness fixed), then
    // execute the SAME turns on two fresh same-seed executors. State-transition
    // content must reproduce exactly; receipt_hash/timestamp may differ.
    let actions = build_actions(&fresh_env(7));

    let first = submit_all(&fresh_env(7), &actions);
    let second = submit_all(&fresh_env(7), &actions);
    assert_eq!(first.len(), second.len());
    for (i, (a, b)) in first.iter().zip(second.iter()).enumerate() {
        assert_eq!(a.turn_hash, b.turn_hash, "turn_hash deterministic (turn {i})");
        assert_eq!(a.pre_state_hash, b.pre_state_hash, "pre_state deterministic (turn {i})");
        assert_eq!(a.post_state_hash, b.post_state_hash, "post_state deterministic (turn {i})");
        assert_eq!(a.effects_hash, b.effects_hash, "effects_hash deterministic (turn {i})");
    }
}
