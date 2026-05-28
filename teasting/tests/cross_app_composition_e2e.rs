//! Cross-app composition e2e — the test that was missing.
//!
//! Every starbridge-app has its own executor-invoking integration test, but
//! nothing composed *multiple* apps into one causal flow. This test drives
//! two apps (identity + nameservice) through a single shared
//! `EmbeddedExecutor` (one ledger, one agent cipherclerk) and asserts two
//! Silver-Vision integration properties the per-app tests cannot:
//!
//!   1. all the apps' turns compose into ONE causal receipt chain — each
//!      receipt links to the previous (`previous_receipt_hash`) across the
//!      app boundary; and
//!   2. re-executing the *same* turns reproduces identical state transitions
//!      (`turn_hash`, pre/post state roots, `effects_hash`) — replay
//!      determinism of the derivable state. (The `receipt_hash`/`timestamp`
//!      legitimately differ run-to-run because the executor stamps wall-clock
//!      time; replay determinism is a property of the state, not the clock.)
//!
//! Flow (one agent, two cells in one ledger):
//!   identity: issue a KYC credential → present it → verify it (accept);
//!   nameservice: register a name (the agent holds a capability to the
//!   registry cell — dregg is a capability mesh, so cross-cell action is
//!   gated on an explicit capability, not mere co-ownership).
//!
//! NOTE: the *credential-gated* nameservice tier
//! (`build_register_with_credential_action`) is intentionally NOT used: its
//! BlindedSet verifier is not yet wired into the embedded executor (tracked
//! separately), so that accept path cannot complete end-to-end. This test
//! uses the achievable accept paths so it is a real, passing composition.

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

fn agent(seed: u8) -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::from_seed([seed; 64]), [42u8; 32])
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

/// Strip `SenderAuthorized` constraints from a program so the embedded
/// executor (no credential-set verifier wired) reaches effect application —
/// the established idiom in the per-app integration tests.
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

/// A fully-set-up shared-ledger environment for the composition: one agent,
/// an identity cell (the primary) and a nameservice registry cell, with the
/// agent granted a capability to reach the registry.
struct Env {
    executor: EmbeddedExecutor,
    cipherclerk: AppCipherclerk,
    identity_cell: CellId,
    ns_cell: CellId,
    owner_pk: [u8; 32],
}

fn fresh_env(seed: u8) -> Env {
    let cipherclerk = agent(seed);
    let executor = EmbeddedExecutor::new(&cipherclerk, "default");

    let identity_cell = executor.cell_id();
    executor.install_program(
        identity_cell,
        CellProgram::Predicate(vec![StateConstraint::Monotonic {
            index: REVOCATION_ROOT_SLOT as u8,
        }]),
    );

    let owner_pk = cipherclerk.public_key().0;
    let ns_obj = Cell::with_balance(owner_pk, *blake3::hash(b"nameservice").as_bytes(), 1_000_000);
    let ns_cell = ns_obj.id();
    executor.ensure_cell(ns_obj).expect("nameservice cell inserts");
    executor.install_program(ns_cell, shape(name_cell_program()));

    // Capability-mesh: the agent's primary cell must hold a capability to the
    // registry cell to act on it (the real flow obtains this via factory-create
    // or a grant turn; granted directly here at setup).
    executor.with_ledger_mut(|ledger| {
        if let Some(agent_cell) = ledger.get_mut(&identity_cell) {
            agent_cell.capabilities.grant(ns_cell, AuthRequired::None);
        }
    });

    Env { executor, cipherclerk, identity_cell, ns_cell, owner_pk }
}

/// Build the ordered composition actions. Randomness in credential issuance /
/// presentation is captured *once* here, so the returned actions replay
/// deterministically when re-submitted.
fn build_actions(env: &Env) -> Vec<Action> {
    let schema = kyc_schema();
    let credential = issue(&issuer_keys(), &schema, [9u8; 32], attributes(), 1_700_000_000, None)
        .expect("issuance succeeds");

    let issue_action =
        build_issue_credential_action(&env.cipherclerk, env.identity_cell, &credential, 1, [0u8; 32]);

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

    let present_action =
        build_present_credential_action(&env.cipherclerk, env.identity_cell, &presentation);

    let verify_opts = VerificationOptions {
        expected_schema: Some(schema),
        expected_disclosure: vec!["verification_level".into()],
        expected_predicates: vec![PredicateRequest::new("verification_level", Predicate::Gte(1))],
        ..Default::default()
    };
    let verify_action = build_verify_presentation_action(
        &env.cipherclerk,
        env.identity_cell,
        &presentation,
        &verify_opts,
    );

    let register_action =
        build_register_action(&env.cipherclerk, env.ns_cell, "alice.dregg", env.owner_pk, 10_000);

    vec![issue_action, present_action, verify_action, register_action]
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
    assert_eq!(receipts.len(), 4, "issue, present, verify, register");

    for (i, r) in receipts.iter().enumerate() {
        assert!(!r.emitted_events.is_empty(), "turn {i} must emit an event");
        assert_eq!(r.action_count, 1, "each composition turn carries one action");
    }

    // The verify step accepted the presentation (accept_flag == 1).
    assert_eq!(
        receipts[2].emitted_events[0].data[1][31], 1,
        "presentation must verify as accepted"
    );

    // THE composition property: all four turns — across the identity and
    // nameservice apps — form ONE causal receipt chain.
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
    let env_for_actions = fresh_env(7);
    let actions = build_actions(&env_for_actions);

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
