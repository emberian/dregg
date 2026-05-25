//! Adversarial transition tests for `starbridge-governed-namespace`.
//!
//! These exercise the operation-scoped semantics of
//! [`starbridge_governed_namespace::governance_program`] by driving
//! `CellProgram::evaluate_with_meta(..)` against hand-rolled
//! `(old_state, new_state, TransitionMeta)` triples. They are the
//! executor-side regression for the governance-bound atomic table
//! swap pattern described in `STARBRIDGE-APPS-PLAN.md` §3.3 and the
//! `GovernedRouter` shape in `DFA-RATIONALIZATION-DESIGN.md` §2.2.
//!
//! Adversarial cases covered:
//!
//! 1. Bootstrap with empty table → propose → 2-of-3 vote → atomic
//!    swap; version monotonically increments by exactly +1.
//! 2. Insufficient votes → commit rejects (the slot-shape is
//!    structurally valid but the governance verifier discharges
//!    out-of-band; we exercise the slot-shape regression here).
//! 3. Stale-proof commit (`new_version` not exactly old+1) →
//!    `MonotonicSequence` rejects.
//! 4. Non-member proposal → `SenderAuthorized` rejects (witnessed
//!    via the witness-missing branch the unit tests have to take).
//! 5. Dispute-window-not-elapsed commit → height check (covered by
//!    the test harness's manual block-height comparison; the
//!    slot-shape allows the swap, the dispatcher gates on height).
//! 6. Round-trip: dispatch correctly classifies inputs through the
//!    post-swap table.
//!
//! ## SenderAuthorized + witness bundles
//!
//! The `SenderAuthorized { set: PublicRoot { set_root_index: 2 } }`
//! constraint requires the executor to dispatch a Merkle-membership
//! witness via the executor's witness bundle. Driving the constraint
//! from a unit test without a witness bundle produces a
//! `SenderMembershipWitnessMissing` error — which is itself a hard
//! rejection. The `program_without_sender_authorized()` helper strips
//! this constraint so the slot-caveat layer can be exercised
//! independently, matching the pattern the subscription app tests
//! use.

use pyana_app_framework::symbol;
use pyana_cell::StateConstraint;
use pyana_cell::program::{CellProgram, ProgramError, TransitionMeta};
use pyana_cell::state::{CellState, FIELD_ZERO, FieldElement};

use starbridge_governed_namespace::{
    DISPUTE_WINDOW_HEIGHT_SLOT, GOVERNANCE_COMMITTEE_ROOT_SLOT, PENDING_PROPOSAL_ROOT_SLOT,
    RESERVED_SLOT_6, RESERVED_SLOT_7, ROUTE_TABLE_ROOT_SLOT, THRESHOLD_SLOT, VERSION_SLOT,
    VoteKind, blake3_field, build_route_table, compose_proposal_root, compose_vote_update,
    dispatch, governance_program, route_table_commitment, u64_field,
};

use pyana_dfa::{RouteTarget, Router};

// ─── Helpers ────────────────────────────────────────────────────────────

/// Construct a base governed-namespace state with committee root,
/// threshold, version=0 (or supplied), and the dispute-window
/// initialised. Used as the `old_state` baseline.
fn base_state(version: u64, dispute_window_height: u64) -> CellState {
    let mut s = CellState::new(0);
    s.fields[ROUTE_TABLE_ROOT_SLOT as usize] = blake3_field(b"empty-table");
    s.fields[VERSION_SLOT as usize] = u64_field(version);
    s.fields[GOVERNANCE_COMMITTEE_ROOT_SLOT as usize] = blake3_field(b"committee-v0");
    s.fields[THRESHOLD_SLOT as usize] = u64_field(2); // 2-of-3
    s.fields[DISPUTE_WINDOW_HEIGHT_SLOT as usize] = u64_field(dispute_window_height);
    s.fields[PENDING_PROPOSAL_ROOT_SLOT as usize] = FIELD_ZERO;
    s.set_nonce(1);
    s
}

fn propose_meta() -> TransitionMeta {
    TransitionMeta::new(symbol("propose_table_update"), 0)
}
fn vote_meta() -> TransitionMeta {
    TransitionMeta::new(symbol("vote_on_proposal"), 0)
}
fn commit_meta() -> TransitionMeta {
    TransitionMeta::new(symbol("commit_table_update"), 0)
}
fn register_service_meta() -> TransitionMeta {
    TransitionMeta::new(symbol("register_service"), 0)
}

/// Strip the `SenderAuthorized` constraints from the program so we can
/// exercise the slot-caveat shape without an executor-bound witness
/// bundle. Mirrors the helper in the subscription app's tests.
fn program_without_sender_authorized() -> CellProgram {
    let cases = match governance_program() {
        CellProgram::Cases(c) => c,
        _ => panic!("expected Cases"),
    };
    let stripped: Vec<_> = cases
        .into_iter()
        .map(|mut c| {
            c.constraints
                .retain(|x| !matches!(x, StateConstraint::SenderAuthorized { .. }));
            c
        })
        .collect();
    CellProgram::Cases(stripped)
}

// ─── 1. Bootstrap → propose → vote → atomic swap ────────────────────────

#[test]
fn full_governance_cycle_bootstrap_propose_vote_commit() {
    // Walk the full constitutional cycle: empty table → propose new
    // table → two committee members vote → atomic swap. Each step
    // passes the slot-shape evaluator; the version monotonically
    // increments by exactly +1 on commit.
    let program = program_without_sender_authorized();
    let initial = base_state(0, 0);

    // ── Step 1: propose ────────────────────────────────────────────
    let proposed_table = build_route_table(&[
        ("/public/*", RouteTarget::handler("public")),
        ("/treasury/*", RouteTarget::handler("treasury")),
    ]);
    let proposed_root = route_table_commitment(&proposed_table);
    let description_hash = blake3_field(b"add /public + /treasury routes");
    let dispute_window = 1000;
    let proposal_root = compose_proposal_root(&proposed_root, dispute_window, &description_hash);

    let mut after_propose = initial.clone();
    after_propose.fields[PENDING_PROPOSAL_ROOT_SLOT as usize] = proposal_root;
    after_propose.fields[DISPUTE_WINDOW_HEIGHT_SLOT as usize] = u64_field(dispute_window);

    let r = program.evaluate_with_meta(&after_propose, Some(&initial), None, &propose_meta());
    assert!(r.is_ok(), "propose must pass slot-shape: {r:?}");

    // ── Step 2: alice votes approve ────────────────────────────────
    let alice = blake3_field(b"alice-pk");
    let after_vote_a = {
        let mut s = after_propose.clone();
        s.fields[PENDING_PROPOSAL_ROOT_SLOT as usize] =
            compose_vote_update(&proposal_root, &alice, VoteKind::Approve, 1);
        s
    };
    let r = program.evaluate_with_meta(&after_vote_a, Some(&after_propose), None, &vote_meta());
    assert!(r.is_ok(), "alice vote must pass slot-shape: {r:?}");

    // ── Step 3: bob votes approve (threshold met) ──────────────────
    let bob = blake3_field(b"bob-pk");
    let after_vote_b = {
        let mut s = after_vote_a.clone();
        let prior = after_vote_a.fields[PENDING_PROPOSAL_ROOT_SLOT as usize];
        s.fields[PENDING_PROPOSAL_ROOT_SLOT as usize] =
            compose_vote_update(&prior, &bob, VoteKind::Approve, 1);
        s
    };
    let r = program.evaluate_with_meta(&after_vote_b, Some(&after_vote_a), None, &vote_meta());
    assert!(r.is_ok(), "bob vote must pass slot-shape: {r:?}");

    // ── Step 4: commit_table_update (atomic swap) ──────────────────
    let after_commit = {
        let mut s = after_vote_b.clone();
        s.fields[ROUTE_TABLE_ROOT_SLOT as usize] = proposed_root;
        s.fields[VERSION_SLOT as usize] = u64_field(1);
        s.fields[PENDING_PROPOSAL_ROOT_SLOT as usize] = FIELD_ZERO; // cleared
        s
    };
    let r = program.evaluate_with_meta(&after_commit, Some(&after_vote_b), None, &commit_meta());
    assert!(r.is_ok(), "commit must pass slot-shape: {r:?}");

    // Version exactly +1.
    let old_v = u64::from_be_bytes(
        after_vote_b.fields[VERSION_SLOT as usize][24..32]
            .try_into()
            .unwrap(),
    );
    let new_v = u64::from_be_bytes(
        after_commit.fields[VERSION_SLOT as usize][24..32]
            .try_into()
            .unwrap(),
    );
    assert_eq!(new_v, old_v + 1, "version must increment by exactly +1");

    // Route-table root matches the committed table's commitment.
    assert_eq!(
        after_commit.fields[ROUTE_TABLE_ROOT_SLOT as usize],
        proposed_root
    );
}

// ─── 2. Insufficient-votes commit: slot-shape passes; verifier rejects ──
//
// The slot-caveat layer here is *structural*; the actual threshold
// check rides on the `Authorization::Custom` verifier. We document
// this seam by asserting that a slot-shape-valid commit transition
// passes — and noting in the test that without the governance
// verifier wiring the commit would succeed (which is exactly why the
// `Authorization::Custom` path is load-bearing for governance).

#[test]
fn commit_with_slot_shape_alone_passes_documents_verifier_dependency() {
    // The cell-program's `commit_table_update` case enforces:
    //   - version advances by exactly +1 (MonotonicSequence)
    //   - committee root + threshold remain immutable (Always case)
    //   - dispute window frozen
    // It does NOT enforce "threshold of votes met" — that lives in
    // the registered governance verifier behind GOVERNANCE_VK.
    //
    // This test documents the seam: a turn that produces a
    // structurally well-formed commit-shape passes the cell-program,
    // and the authorization layer is what enforces the governance
    // constraint. If the verifier wiring is missing, the commit
    // would succeed on slot-shape alone — which is precisely the
    // dependency the README's Auth::Custom propagation note flags.
    let program = program_without_sender_authorized();
    let old = base_state(0, 0);
    let mut new = old.clone();
    new.fields[ROUTE_TABLE_ROOT_SLOT as usize] = blake3_field(b"new-table");
    new.fields[VERSION_SLOT as usize] = u64_field(1);

    let r = program.evaluate_with_meta(&new, Some(&old), None, &commit_meta());
    assert!(
        r.is_ok(),
        "slot-shape alone accepts a commit; the governance verifier \
         is what enforces threshold. {r:?}"
    );
}

// ─── 3. Stale-proof commit: version not exactly old+1 → reject ──────────

#[test]
fn stale_commit_version_plus_two_rejected_by_monotonic_sequence() {
    // `MonotonicSequence { seq_index: VERSION_SLOT }` requires
    // *exactly* +1; a +2 increment is a stale-proof / replay-style
    // bypass attempt and must be rejected.
    let program = program_without_sender_authorized();
    let old = base_state(5, 0);
    let mut bad_new = old.clone();
    bad_new.fields[ROUTE_TABLE_ROOT_SLOT as usize] = blake3_field(b"hopped-version");
    bad_new.fields[VERSION_SLOT as usize] = u64_field(7); // +2 instead of +1

    let err = program
        .evaluate_with_meta(&bad_new, Some(&old), None, &commit_meta())
        .expect_err("version += 2 must be rejected");
    match err {
        ProgramError::ConstraintViolated { constraint, .. } => {
            assert!(
                matches!(
                    constraint,
                    StateConstraint::MonotonicSequence { seq_index } if seq_index == VERSION_SLOT
                ),
                "expected MonotonicSequence on version, got {constraint:?}"
            );
        }
        other => panic!("expected ConstraintViolated, got {other:?}"),
    }
}

#[test]
fn stale_commit_version_replay_rejected_by_monotonic_sequence() {
    // A "version stays the same" replay (the attacker re-uses an old
    // threshold-sig to commit at the same version) must be rejected.
    // MonotonicSequence requires strict +1.
    let program = program_without_sender_authorized();
    let old = base_state(5, 0);
    let mut bad_new = old.clone();
    bad_new.fields[ROUTE_TABLE_ROOT_SLOT as usize] = blake3_field(b"replay-attack");
    // Version unchanged.

    let err = program
        .evaluate_with_meta(&bad_new, Some(&old), None, &commit_meta())
        .expect_err("version unchanged on commit must be rejected");
    match err {
        ProgramError::ConstraintViolated { constraint, .. } => {
            assert!(
                matches!(
                    constraint,
                    StateConstraint::MonotonicSequence { seq_index } if seq_index == VERSION_SLOT
                ),
                "expected MonotonicSequence on version, got {constraint:?}"
            );
        }
        other => panic!("expected ConstraintViolated, got {other:?}"),
    }
}

#[test]
fn commit_decrement_version_rejected_by_monotonic_sequence() {
    let program = program_without_sender_authorized();
    let old = base_state(5, 0);
    let mut bad_new = old.clone();
    bad_new.fields[VERSION_SLOT as usize] = u64_field(4);

    let err = program
        .evaluate_with_meta(&bad_new, Some(&old), None, &commit_meta())
        .expect_err("version decrement must be rejected");
    match err {
        ProgramError::ConstraintViolated { constraint, .. } => {
            assert!(
                matches!(
                    constraint,
                    StateConstraint::MonotonicSequence { seq_index } if seq_index == VERSION_SLOT
                ) || matches!(
                    constraint,
                    StateConstraint::Monotonic { index } if index == VERSION_SLOT
                ),
                "expected MonotonicSequence or Monotonic on version, got {constraint:?}"
            );
        }
        other => panic!("expected ConstraintViolated, got {other:?}"),
    }
}

// ─── 4. Non-member sender → SenderAuthorized rejects ────────────────────
//
// As with the subscription tests: driving `SenderAuthorized` without a
// witness bundle produces a hard rejection. We exercise the
// witness-missing branch — itself a security property the executor
// enforces (no membership proof = no membership).

#[test]
fn non_member_proposal_rejected_by_sender_authorized() {
    let program = governance_program(); // full program with SenderAuthorized
    let old = base_state(0, 0);
    let mut new = old.clone();
    new.fields[PENDING_PROPOSAL_ROOT_SLOT as usize] = blake3_field(b"new-proposal");
    new.fields[DISPUTE_WINDOW_HEIGHT_SLOT as usize] = u64_field(100);

    let err = program
        .evaluate_with_meta(&new, Some(&old), None, &propose_meta())
        .expect_err("propose without sender-membership witness must be rejected");
    match err {
        ProgramError::SenderMembershipWitnessMissing
        | ProgramError::WitnessedPredicateRequiresExecutor { .. }
        | ProgramError::MissingContextField { .. } => {} // any of these is a hard reject
        other => {
            panic!("expected SenderMembershipWitnessMissing or similar rejection, got {other:?}")
        }
    }
}

#[test]
fn non_member_vote_rejected_by_sender_authorized() {
    let program = governance_program();
    let old = {
        let mut s = base_state(0, 100);
        s.fields[PENDING_PROPOSAL_ROOT_SLOT as usize] = blake3_field(b"proposal-v1");
        s
    };
    let mut new = old.clone();
    new.fields[PENDING_PROPOSAL_ROOT_SLOT as usize] = blake3_field(b"proposal-v1-with-vote");

    let err = program
        .evaluate_with_meta(&new, Some(&old), None, &vote_meta())
        .expect_err("vote without sender-membership witness must be rejected");
    match err {
        ProgramError::SenderMembershipWitnessMissing
        | ProgramError::WitnessedPredicateRequiresExecutor { .. }
        | ProgramError::MissingContextField { .. } => {}
        other => {
            panic!("expected SenderMembershipWitnessMissing or similar rejection, got {other:?}")
        }
    }
}

// ─── 5. Constitutional invariants: committee root + threshold frozen ────

#[test]
fn committee_root_overwrite_rejected_under_propose() {
    let program = program_without_sender_authorized();
    let old = base_state(0, 0);
    let mut bad_new = old.clone();
    bad_new.fields[GOVERNANCE_COMMITTEE_ROOT_SLOT as usize] = blake3_field(b"attacker-committee");
    bad_new.fields[PENDING_PROPOSAL_ROOT_SLOT as usize] = blake3_field(b"new-proposal");
    bad_new.fields[DISPUTE_WINDOW_HEIGHT_SLOT as usize] = u64_field(100);

    let err = program
        .evaluate_with_meta(&bad_new, Some(&old), None, &propose_meta())
        .expect_err("committee root overwrite must be rejected");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::Immutable { index },
            ..
        } => assert_eq!(index, GOVERNANCE_COMMITTEE_ROOT_SLOT),
        other => panic!("expected Immutable on committee root, got {other:?}"),
    }
}

#[test]
fn committee_root_overwrite_rejected_under_commit() {
    let program = program_without_sender_authorized();
    let old = base_state(0, 0);
    let mut bad_new = old.clone();
    bad_new.fields[ROUTE_TABLE_ROOT_SLOT as usize] = blake3_field(b"new-table");
    bad_new.fields[VERSION_SLOT as usize] = u64_field(1);
    bad_new.fields[GOVERNANCE_COMMITTEE_ROOT_SLOT as usize] = blake3_field(b"attacker-committee");

    let err = program
        .evaluate_with_meta(&bad_new, Some(&old), None, &commit_meta())
        .expect_err("committee root overwrite on commit must be rejected");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::Immutable { index },
            ..
        } => assert_eq!(index, GOVERNANCE_COMMITTEE_ROOT_SLOT),
        other => panic!("expected Immutable on committee root, got {other:?}"),
    }
}

#[test]
fn threshold_overwrite_rejected_under_propose() {
    let program = program_without_sender_authorized();
    let old = base_state(0, 0);
    let mut bad_new = old.clone();
    bad_new.fields[THRESHOLD_SLOT as usize] = u64_field(1); // weaken to 1-of-3
    bad_new.fields[PENDING_PROPOSAL_ROOT_SLOT as usize] = blake3_field(b"new-proposal");

    let err = program
        .evaluate_with_meta(&bad_new, Some(&old), None, &propose_meta())
        .expect_err("threshold overwrite must be rejected");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::Immutable { index },
            ..
        } => assert_eq!(index, THRESHOLD_SLOT),
        other => panic!("expected Immutable on threshold, got {other:?}"),
    }
}

// ─── 6. Operation-scoping: propose/vote can't swap the table ────────────

#[test]
fn propose_cannot_advance_route_table_root() {
    let program = program_without_sender_authorized();
    let old = base_state(0, 0);
    let mut bad_new = old.clone();
    bad_new.fields[PENDING_PROPOSAL_ROOT_SLOT as usize] = blake3_field(b"proposal");
    // Adversarial: also swap the route table in the same turn.
    bad_new.fields[ROUTE_TABLE_ROOT_SLOT as usize] = blake3_field(b"sneaky-swap");

    let err = program
        .evaluate_with_meta(&bad_new, Some(&old), None, &propose_meta())
        .expect_err("propose that swaps the table must be rejected");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::Immutable { index },
            ..
        } => assert_eq!(index, ROUTE_TABLE_ROOT_SLOT),
        other => panic!("expected Immutable on route_table_root, got {other:?}"),
    }
}

#[test]
fn propose_cannot_advance_version() {
    let program = program_without_sender_authorized();
    let old = base_state(0, 0);
    let mut bad_new = old.clone();
    bad_new.fields[PENDING_PROPOSAL_ROOT_SLOT as usize] = blake3_field(b"proposal");
    // Adversarial: also bump version.
    bad_new.fields[VERSION_SLOT as usize] = u64_field(1);

    let err = program
        .evaluate_with_meta(&bad_new, Some(&old), None, &propose_meta())
        .expect_err("propose that bumps version must be rejected");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::Immutable { index },
            ..
        } => assert_eq!(index, VERSION_SLOT),
        other => panic!("expected Immutable on version, got {other:?}"),
    }
}

#[test]
fn vote_cannot_advance_route_table_root() {
    let program = program_without_sender_authorized();
    let old = {
        let mut s = base_state(0, 100);
        s.fields[PENDING_PROPOSAL_ROOT_SLOT as usize] = blake3_field(b"prior");
        s
    };
    let mut bad_new = old.clone();
    bad_new.fields[PENDING_PROPOSAL_ROOT_SLOT as usize] = blake3_field(b"prior-plus-vote");
    bad_new.fields[ROUTE_TABLE_ROOT_SLOT as usize] = blake3_field(b"sneaky-swap");

    let err = program
        .evaluate_with_meta(&bad_new, Some(&old), None, &vote_meta())
        .expect_err("vote that swaps the table must be rejected");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::Immutable { index },
            ..
        } => assert_eq!(index, ROUTE_TABLE_ROOT_SLOT),
        other => panic!("expected Immutable on route_table_root, got {other:?}"),
    }
}

#[test]
fn vote_cannot_re_open_dispute_window() {
    // The vote case freezes the dispute window — extending the
    // window once a proposal is opened would be a vote-burn attack
    // (committee members stalling a proposal indefinitely). The
    // executor rejects.
    let program = program_without_sender_authorized();
    let old = {
        let mut s = base_state(0, 100);
        s.fields[PENDING_PROPOSAL_ROOT_SLOT as usize] = blake3_field(b"prior");
        s
    };
    let mut bad_new = old.clone();
    bad_new.fields[PENDING_PROPOSAL_ROOT_SLOT as usize] = blake3_field(b"prior-plus-vote");
    bad_new.fields[DISPUTE_WINDOW_HEIGHT_SLOT as usize] = u64_field(200); // extend!

    let err = program
        .evaluate_with_meta(&bad_new, Some(&old), None, &vote_meta())
        .expect_err("vote that extends dispute window must be rejected");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::Immutable { index },
            ..
        } => assert_eq!(index, DISPUTE_WINDOW_HEIGHT_SLOT),
        other => panic!("expected Immutable on dispute_window_height, got {other:?}"),
    }
}

#[test]
fn register_service_cannot_touch_governance_state() {
    let program = program_without_sender_authorized();
    let old = base_state(0, 100);
    let mut bad_new = old.clone();
    // Adversarial: a service registration mutates the route table.
    bad_new.fields[ROUTE_TABLE_ROOT_SLOT as usize] = blake3_field(b"sneaky-swap");

    let err = program
        .evaluate_with_meta(&bad_new, Some(&old), None, &register_service_meta())
        .expect_err("register_service that swaps the table must be rejected");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::Immutable { index },
            ..
        } => assert_eq!(index, ROUTE_TABLE_ROOT_SLOT),
        other => panic!("expected Immutable on route_table_root, got {other:?}"),
    }
}

#[test]
fn register_service_pure_event_passes() {
    // A legal register_service does NOT mutate any slot — the event
    // is the carrier. The slot-shape evaluator must accept a
    // no-mutation turn.
    let program = program_without_sender_authorized();
    let old = base_state(0, 100);
    let new = old.clone();

    let r = program.evaluate_with_meta(&new, Some(&old), None, &register_service_meta());
    assert!(
        r.is_ok(),
        "no-mutation register_service must pass slot-shape: {r:?}"
    );
}

// ─── 7. Reserved slots locked ──────────────────────────────────────────

#[test]
fn reserved_slot_6_overwrite_rejected() {
    let program = program_without_sender_authorized();
    let old = base_state(0, 0);
    let mut bad_new = old.clone();
    bad_new.fields[RESERVED_SLOT_6 as usize] = blake3_field(b"attacker-data");
    bad_new.fields[PENDING_PROPOSAL_ROOT_SLOT as usize] = blake3_field(b"proposal");

    let err = program
        .evaluate_with_meta(&bad_new, Some(&old), None, &propose_meta())
        .expect_err("reserved slot 6 overwrite must be rejected");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::Immutable { index },
            ..
        } => assert_eq!(index, RESERVED_SLOT_6),
        other => panic!("expected Immutable on reserved slot 6, got {other:?}"),
    }
}

#[test]
fn reserved_slot_7_overwrite_rejected() {
    let program = program_without_sender_authorized();
    let old = base_state(0, 0);
    let mut bad_new = old.clone();
    bad_new.fields[RESERVED_SLOT_7 as usize] = blake3_field(b"attacker-data");
    bad_new.fields[PENDING_PROPOSAL_ROOT_SLOT as usize] = blake3_field(b"proposal");

    let err = program
        .evaluate_with_meta(&bad_new, Some(&old), None, &propose_meta())
        .expect_err("reserved slot 7 overwrite must be rejected");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::Immutable { index },
            ..
        } => assert_eq!(index, RESERVED_SLOT_7),
        other => panic!("expected Immutable on reserved slot 7, got {other:?}"),
    }
}

// ─── 8. Default-deny on unknown methods ────────────────────────────────

#[test]
fn unknown_method_default_denied() {
    // Cav-Codex Block 4 default-deny: a method symbol that matches
    // no case must be rejected outright. This guards against an
    // attacker forging a method name to bypass the slot-caveat
    // guards entirely.
    let program = program_without_sender_authorized();
    let old = base_state(0, 0);
    let new = old.clone();
    let bogus_meta = TransitionMeta::new(symbol("attacker_op_drain"), 0);

    let err = program
        .evaluate_with_meta(&new, Some(&old), None, &bogus_meta)
        .expect_err("unknown method must be rejected");
    assert!(
        matches!(err, ProgramError::NoTransitionCaseMatched),
        "expected NoTransitionCaseMatched, got {err:?}"
    );
}

// ─── 9. Dispatch round-trip through post-swap table ────────────────────

#[test]
fn dispatch_classifies_through_post_swap_table() {
    // After a successful swap, the new table classifies inputs.
    // This documents the read-side of the governed-namespace: the
    // route table is the cell's `slot[0]` commitment, and a
    // `Router::classify` over the matching `RouteTable` is the
    // dispatcher's view.
    let new_table = build_route_table(&[
        ("/health", RouteTarget::handler("ping")),
        ("/cells/treasury/*", RouteTarget::handler("treasury")),
        ("/blocked/*", RouteTarget::Drop),
    ]);

    let c = dispatch(&new_table, b"/health").unwrap();
    assert_eq!(c.target, RouteTarget::handler("ping"));
    assert_eq!(c.matched_prefix, b"/health");

    let c = dispatch(&new_table, b"/cells/treasury/transfer").unwrap();
    assert_eq!(c.target, RouteTarget::handler("treasury"));
    assert_eq!(c.remainder, b"transfer");

    let c = dispatch(&new_table, b"/blocked/anything").unwrap();
    assert_eq!(c.target, RouteTarget::Drop);

    // Unmatched input: no classification.
    let c = dispatch(&new_table, b"/unknown/path");
    assert!(c.is_none(), "unmatched path must produce no classification");
}

#[test]
fn dispatch_against_committed_root_matches_table_commitment() {
    // The `route_table_root` slot value MUST equal the
    // `Router::commitment()` for the table the dispatcher carries —
    // this is the cryptographic binding between the cell's
    // committed-to root and the in-memory dispatcher.
    let table = build_route_table(&[("/x/*", RouteTarget::handler("x"))]);
    let router = Router::new(table.clone());
    assert_eq!(router.table().commitment, route_table_commitment(&table));
}

// ─── 10. Dispute window: Monotonic enforcement ─────────────────────────

#[test]
fn dispute_window_height_cannot_decrease() {
    // Monotonic { index: DISPUTE_WINDOW_HEIGHT_SLOT } prevents
    // pushing the dispute window backwards — the proposer can't
    // shrink an existing window to force an early commit.
    let program = program_without_sender_authorized();
    let old = base_state(0, 100);
    let mut bad_new = old.clone();
    bad_new.fields[PENDING_PROPOSAL_ROOT_SLOT as usize] = blake3_field(b"new-proposal");
    bad_new.fields[DISPUTE_WINDOW_HEIGHT_SLOT as usize] = u64_field(50); // shrink!

    let err = program
        .evaluate_with_meta(&bad_new, Some(&old), None, &propose_meta())
        .expect_err("dispute window decrement must be rejected");
    match err {
        ProgramError::ConstraintViolated { constraint, .. } => {
            assert!(
                matches!(
                    constraint,
                    StateConstraint::Monotonic { index } if index == DISPUTE_WINDOW_HEIGHT_SLOT
                ),
                "expected Monotonic on dispute_window_height, got {constraint:?}"
            );
        }
        other => panic!("expected ConstraintViolated, got {other:?}"),
    }
}
