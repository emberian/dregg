//! Cross-app composition gate — identity + nameservice + governed-namespace.
//!
//! Extends the three-app composition test (`cross_app_composition_e2e.rs`)
//! with a fourth app: **governed-namespace**, whose governance flow
//! (propose → vote → commit, then register_service) runs on its own cell in
//! the same shared `EmbeddedExecutor` and composes into ONE causal receipt
//! chain with the identity and nameservice steps that precede it.
//!
//! Properties asserted (mirroring the reference test):
//!
//!   1. All turns across identity + nameservice + governed-namespace form ONE
//!      causal receipt chain: each receipt links to the previous via
//!      `previous_receipt_hash`, including across every app boundary.
//!   2. Re-executing the same turns on two fresh same-seed executors
//!      reproduces identical state transitions (`turn_hash`, `pre_state_hash`,
//!      `post_state_hash`, `effects_hash`) — replay determinism. (Receipt
//!      hash and timestamp legitimately differ run-to-run due to wall-clock
//!      stamping.)
//!
//! Flow (one agent; identity cell + nameservice cell + governed-namespace
//! cell in one ledger; the agent holds a capability to each non-primary cell):
//!   identity:           issue a KYC credential → present it → verify it
//!   nameservice:        register a name
//!   governed-namespace: propose_table_update → vote_on_proposal (×2) →
//!                       register_service
//!
//! Note: `commit_table_update` carries `Authorization::Custom` and requires a
//! registered governance verifier that is not wired in the embedded executor.
//! The test uses the achievable accept paths (propose + vote + register_service)
//! so the gate is real. The seam is documented inline.

use dregg_app_framework::{AgentCipherclerk, AppCipherclerk, CellId, EmbeddedExecutor};
use dregg_cell::permissions::{AuthRequired, Permissions};
use dregg_cell::program::{CellProgram, TransitionCase, TransitionGuard};
use dregg_cell::state::CellState;
use dregg_cell::{Cell, StateConstraint};
use dregg_turn::{Action, TurnReceipt};

use starbridge_identity::{
    AttrValue, CredentialAttributes, IssuerKeys, Predicate, PredicateRequest, PresentationOptions,
    REVOCATION_ROOT_SLOT, VerificationOptions, build_issue_credential_action,
    build_present_credential_action, build_verify_presentation_action, issue, kyc_schema, present,
};
use starbridge_nameservice::{build_register_action, name_cell_program};

use starbridge_governed_namespace::{
    DISPUTE_WINDOW_HEIGHT_SLOT, GOVERNANCE_COMMITTEE_ROOT_SLOT, PENDING_PROPOSAL_ROOT_SLOT,
    ROUTE_TABLE_ROOT_SLOT, THRESHOLD_SLOT, VERSION_SLOT, VoteKind, blake3_field,
    build_propose_table_update_action, build_register_service_action,
    build_route_table, build_vote_on_proposal_action, governance_program,
    route_table_commitment, u64_field,
};

use dregg_dfa::RouteTarget;

fn agent(seed: u8) -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::from_seed([seed; 64]), [42u8; 32])
}

fn issuer_keys() -> IssuerKeys {
    IssuerKeys::new(
        [100u8; 32],
        [
            3, 154, 242, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0,
        ],
        b"composition-governed-test",
        "starbridge-identity",
    )
}

fn attributes() -> CredentialAttributes {
    CredentialAttributes::new()
        .with("given_name", AttrValue::Text("Alice".into()))
        .with("verification_level", AttrValue::Integer(2))
}

/// Strip `SenderAuthorized` constraints so the embedded executor reaches
/// effect application. Matches the idiom in `cross_app_composition_e2e.rs`
/// and `integration_propose_vote_commit.rs`.
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
    gov_cell: CellId,
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

    // nameservice cell.
    let ns_obj = Cell::with_balance(owner_pk, *blake3::hash(b"nameservice-gov").as_bytes(), 1_000_000);
    let ns_cell = ns_obj.id();
    executor.ensure_cell(ns_obj).expect("ns cell inserts");
    executor.install_program(ns_cell, shape(name_cell_program()));

    // governed-namespace cell: initialised with constitutional state exactly
    // as `init_namespace_cell` does in `integration_propose_vote_commit.rs`.
    let gov_obj = Cell::with_balance(owner_pk, *blake3::hash(b"governed-namespace").as_bytes(), 1_000_000);
    let gov_cell = gov_obj.id();
    executor.ensure_cell(gov_obj).expect("gov cell inserts");

    executor.with_ledger_mut(|ledger| {
        let cell = ledger.get_mut(&gov_cell).expect("gov cell exists");

        // Install the stripped governance program (no SenderAuthorized).
        cell.program = shape(governance_program());

        // Open all permissions so a single cipherclerk can drive propose/vote.
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

        // Seed the constitutional state: committee root + threshold fixed,
        // version 0, pending proposal empty.
        let mut state = CellState::new(1_000_000);
        state.fields[ROUTE_TABLE_ROOT_SLOT as usize] = blake3_field(b"empty-table");
        state.fields[VERSION_SLOT as usize] = u64_field(0);
        state.fields[GOVERNANCE_COMMITTEE_ROOT_SLOT as usize] = blake3_field(b"committee-v0");
        state.fields[THRESHOLD_SLOT as usize] = u64_field(2);
        state.fields[DISPUTE_WINDOW_HEIGHT_SLOT as usize] = u64_field(0);
        state.fields[PENDING_PROPOSAL_ROOT_SLOT as usize] = [0u8; 32];
        cell.state = state;
    });

    // Grant the primary cell capabilities to reach the two app cells.
    executor.with_ledger_mut(|ledger| {
        if let Some(agent_cell) = ledger.get_mut(&identity_cell) {
            agent_cell.capabilities.grant(ns_cell, AuthRequired::None);
            agent_cell.capabilities.grant(gov_cell, AuthRequired::None);
        }
    });

    Env { executor, cipherclerk, identity_cell, ns_cell, gov_cell, owner_pk }
}

/// Build the ordered composition actions.
///
/// Randomness in credential issuance / presentation is captured once here,
/// so the returned actions replay deterministically when re-submitted.
///
/// Governance flow: propose_table_update → vote ×2 → register_service.
/// `commit_table_update` requires `Authorization::Custom` + a registered
/// governance verifier that is NOT wired in the embedded executor, so it is
/// intentionally excluded from the composition chain. The seam is documented
/// inline.
fn build_actions(env: &Env) -> Vec<Action> {
    let cc = &env.cipherclerk;

    // ── identity: issue → present → verify ──────────────────────────────
    let schema = kyc_schema();
    let credential = issue(
        &issuer_keys(),
        &schema,
        [9u8; 32],
        attributes(),
        1_700_000_000,
        None,
    )
    .expect("issuance succeeds");
    let issue_action =
        build_issue_credential_action(cc, env.identity_cell, &credential, 1, [0u8; 32]);

    let opts = PresentationOptions::new()
        .disclose("verification_level")
        .predicate(PredicateRequest::new("verification_level", Predicate::Gte(1)));
    let presentation = present(
        &credential,
        &dregg_token::AuthRequest {
            action: Some("read".into()),
            app_id: Some("composition-governed-test".into()),
            user_id: Some(
                "0909090909090909090909090909090909090909090909090909090909090909".into(),
            ),
            now: Some(1_700_000_000),
            ..Default::default()
        },
        &opts,
    )
    .expect("presentation builds");
    let present_action =
        build_present_credential_action(cc, env.identity_cell, &presentation);

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

    // ── governed-namespace: propose → vote ×2 → register_service ───────
    //
    // The governance flow as driven by `integration_propose_vote_commit.rs`:
    //   1. propose_table_update — opens a new route-table proposal.
    //   2. vote_on_proposal (×2) — the proposer casts two votes on behalf of
    //      the threshold quorum (permissions are AuthRequired::None, so one
    //      cipherclerk can drive all turns; the vote-folding logic is identical
    //      regardless of which keypair signs).
    //   3. register_service — pure-event turn (no governance-slot mutation);
    //      reaches the executor unconditionally.
    //
    // commit_table_update is excluded: it constructs Authorization::Custom and
    // requires the governance verifier registered under GOVERNANCE_VK, which is
    // NOT wired in the embedded executor. The pending_proposal_root slot is not
    // cleared by the test (no commit); this does not affect the composition
    // chain linkage.

    let new_table = build_route_table(&[
        ("/public/*", RouteTarget::handler("public")),
        ("/treasury/*", RouteTarget::handler("treasury")),
    ]);

    let propose_action = build_propose_table_update_action(
        cc,
        env.gov_cell,
        &new_table,
        1_000, // dispute_window_height
        "composition-test: add public + treasury routes",
    );

    // The proposal_root is the first field of the proposal-opened event
    // (data[0]) emitted by the propose turn. We must pre-compute it here so
    // build_actions can be called before submit_all without executor state.
    let proposed_root = route_table_commitment(&new_table);
    let description_hash = blake3_field(b"composition-test: add public + treasury routes");
    let proposal_root = starbridge_governed_namespace::compose_proposal_root(
        &proposed_root,
        1_000,
        &description_hash,
    );

    // First vote: proposer votes approve against the initial proposal_root.
    let vote_a_action = build_vote_on_proposal_action(
        cc,
        env.gov_cell,
        proposal_root,
        VoteKind::Approve,
        1,
    );

    // Second vote: proposer votes again (using the updated proposal_root that
    // vote_a produces). Mirrors the pattern in `integration_propose_vote_commit.rs`.
    let after_vote_a_root = starbridge_governed_namespace::compose_vote_update(
        &proposal_root,
        &blake3_field(&cc.public_key().0),
        VoteKind::Approve,
        1,
    );
    let vote_b_action = build_vote_on_proposal_action(
        cc,
        env.gov_cell,
        after_vote_a_root,
        VoteKind::Approve,
        1,
    );

    // register_service: pure-event; no governance-slot mutation needed.
    let target_cell = CellId::from_bytes([0xCCu8; 32]);
    let register_service_action =
        build_register_service_action(cc, env.gov_cell, "/treasury/main", target_cell);

    vec![
        issue_action,
        present_action,
        verify_action,
        register_action,
        propose_action,
        vote_a_action,
        vote_b_action,
        register_service_action,
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
fn cross_app_composition_governed_chains_one_receipt_chain_and_emits_events() {
    let env = fresh_env(13);
    let actions = build_actions(&env);
    let receipts = submit_all(&env, &actions);

    // 3 identity + 1 nameservice + 4 governed-namespace (propose, vote×2, register)
    assert_eq!(
        receipts.len(),
        8,
        "issue, present, verify, register, propose, vote_a, vote_b, register_service"
    );

    for (i, r) in receipts.iter().enumerate() {
        assert!(!r.emitted_events.is_empty(), "turn {i} must emit at least one event");
        assert_eq!(r.action_count, 1, "each composition turn carries one action");
    }

    // identity verify (turn 2) accepted the presentation.
    assert_eq!(
        receipts[2].emitted_events[0].data[1][31],
        1,
        "presentation must verify as accepted"
    );

    // governed-namespace propose (turn 4) emits proposal-opened with the
    // correct proposed route-table commitment in data[1].
    let new_table = build_route_table(&[
        ("/public/*", RouteTarget::handler("public")),
        ("/treasury/*", RouteTarget::handler("treasury")),
    ]);
    let expected_proposed_root = route_table_commitment(&new_table);
    assert_eq!(
        receipts[4].emitted_events[0].data[1],
        expected_proposed_root,
        "proposal-opened event must carry the proposed route-table commitment"
    );

    // governed-namespace register_service (turn 7) emits service-registered
    // with the canonical /treasury/main path hash.
    let expected_path_hash = blake3_field(b"/treasury/main");
    assert_eq!(
        receipts[7].emitted_events[0].data[0],
        expected_path_hash,
        "service-registered event must carry canonical path hash"
    );

    // THE composition property: all eight turns — across identity, nameservice,
    // and governed-namespace — form ONE causal receipt chain.
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
fn cross_app_composition_governed_state_transitions_are_deterministic_on_replay() {
    // Build the actions once (credential/presentation randomness fixed), then
    // execute the SAME turns on two fresh same-seed executors. State-transition
    // content must reproduce exactly; receipt_hash/timestamp may differ.
    let actions = build_actions(&fresh_env(13));

    let first = submit_all(&fresh_env(13), &actions);
    let second = submit_all(&fresh_env(13), &actions);

    assert_eq!(first.len(), second.len());
    for (i, (a, b)) in first.iter().zip(second.iter()).enumerate() {
        assert_eq!(a.turn_hash, b.turn_hash, "turn_hash deterministic (turn {i})");
        assert_eq!(
            a.pre_state_hash, b.pre_state_hash,
            "pre_state deterministic (turn {i})"
        );
        assert_eq!(
            a.post_state_hash, b.post_state_hash,
            "post_state deterministic (turn {i})"
        );
        assert_eq!(
            a.effects_hash, b.effects_hash,
            "effects_hash deterministic (turn {i})"
        );
    }
}
