//! Adversarial transition tests for the guard subject-account program.
//!
//! These exercise the operation-scoped semantics of
//! [`starbridge_guard::guard_program`] by driving
//! `CellProgram::evaluate_with_meta(..)` against hand-rolled
//! `(old_state, new_state, TransitionMeta)` triples — the executor-side regression
//! for the two teeth the mission requires:
//!
//!   1. **the consume ceiling** — a consume that would push `consumed` past the
//!      frozen `ceiling` is refused (the in-band `402`/`429`);
//!   2. **the standing gate** — `standing` moves ONLY through a governance-gated
//!      `set_standing` turn: the `consume_quota` case FREEZES it (`Immutable`), an
//!      unknown method is default-denied, and `set_standing` carries a
//!      `SenderAuthorized(PublicRoot)` clause a bare self-write cannot satisfy (the
//!      witness-missing branch — itself the security property that no membership
//!      proof = no standing move).
//!
//! ## SenderAuthorized + witness bundles
//!
//! Driving `SenderAuthorized` from a unit test without a witness bundle produces a
//! `SenderMembershipWitnessMissing` (a hard rejection). The
//! `program_without_sender_authorized()` helper strips that constraint so the
//! slot-caveat shape can be exercised independently — mirroring
//! `starbridge-governed-namespace`'s governance tests. The witnessed ACCEPT path (a
//! real governance turn commits) and the non-governance REJECT are exercised on the
//! real executor in `tests/governance_executor.rs`.

use dregg_app_framework::{field_from_u64, symbol};
use dregg_cell::StateConstraint;
use dregg_cell::program::{CellProgram, ProgramError, TransitionMeta};
use dregg_cell::state::CellState;

use starbridge_guard::{
    CEILING_SLOT, CONSUMED_SLOT, GOVERNANCE_ROOT_SLOT, STANDING_FLAGGED, STANDING_GOOD,
    STANDING_SLOT, STANDING_SUSPENDED, SUBJECT_SLOT, guard_program,
};

// ─── Helpers ────────────────────────────────────────────────────────────

/// A base subject-account state: `consumed` / `ceiling` / `standing` set, plus a
/// non-zero governance root + subject (the `WriteOnce` constitution). Used as the
/// `old_state` baseline.
fn base_state(consumed: u64, ceiling: u64, standing: u64) -> CellState {
    let mut s = CellState::new(0);
    s.fields[CONSUMED_SLOT as usize] = field_from_u64(consumed);
    s.fields[CEILING_SLOT as usize] = field_from_u64(ceiling);
    s.fields[STANDING_SLOT as usize] = field_from_u64(standing);
    s.fields[GOVERNANCE_ROOT_SLOT as usize] = field_from_u64(0xABCD);
    s.fields[SUBJECT_SLOT as usize] = field_from_u64(0x5175);
    s.set_nonce(1);
    s
}

fn consume_meta() -> TransitionMeta {
    TransitionMeta::new(symbol("consume_quota"), 0)
}
fn set_standing_meta() -> TransitionMeta {
    TransitionMeta::new(symbol("set_standing"), 0)
}

/// Strip the `SenderAuthorized` constraints so we can exercise the `set_standing`
/// slot-caveat shape without an executor-bound witness bundle. Mirrors the helper in
/// governed-namespace's tests.
fn program_without_sender_authorized() -> CellProgram {
    let cases = match guard_program() {
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

// ─── 1. The consume ceiling (tooth 1, program level) ─────────────────────

#[test]
fn honest_consume_under_the_ceiling_passes() {
    let program = guard_program();
    let old = base_state(0, 3, STANDING_GOOD);
    let mut new = old.clone();
    new.fields[CONSUMED_SLOT as usize] = field_from_u64(1);
    let r = program.evaluate_with_meta(&new, Some(&old), None, &consume_meta());
    assert!(r.is_ok(), "an in-budget consume must pass: {r:?}");
}

#[test]
fn consume_over_the_ceiling_is_refused_in_band() {
    let program = guard_program();
    let old = base_state(3, 3, STANDING_GOOD);
    let mut bad_new = old.clone();
    // 3 → 4 overruns the ceiling of 3.
    bad_new.fields[CONSUMED_SLOT as usize] = field_from_u64(4);
    let err = program
        .evaluate_with_meta(&bad_new, Some(&old), None, &consume_meta())
        .expect_err("an over-ceiling consume must be refused — the CEILING TOOTH");
    let msg = format!("{err:?}").to_lowercase();
    assert!(
        msg.contains("lte") || msg.contains("field") || msg.contains("constraint"),
        "refusal must cite the consumed ≤ ceiling budget, got: {msg}"
    );
}

// ─── 2. The standing gate (tooth 2, program level) ───────────────────────

#[test]
fn a_consume_cannot_move_standing_the_self_write_is_frozen() {
    // A subject metering a consume that ALSO tries to flip its own standing
    // good → flagged is refused: the `consume_quota` case freezes STANDING
    // (`Immutable`), so a subject can never launder a standing self-write through
    // the metering path.
    let program = guard_program();
    let old = base_state(0, 3, STANDING_GOOD);
    let mut bad_new = old.clone();
    bad_new.fields[CONSUMED_SLOT as usize] = field_from_u64(1);
    bad_new.fields[STANDING_SLOT as usize] = field_from_u64(STANDING_FLAGGED);
    let err = program
        .evaluate_with_meta(&bad_new, Some(&old), None, &consume_meta())
        .expect_err("a consume that moves standing must be refused by Immutable");
    let msg = format!("{err:?}").to_lowercase();
    assert!(
        msg.contains("immutable") || msg.contains("constraint"),
        "refusal must cite the frozen standing slot, got: {msg}"
    );
}

#[test]
fn set_standing_without_a_membership_witness_is_refused() {
    // THE decisive standing tooth: a `set_standing` that flips good → suspended
    // carries the `SenderAuthorized(PublicRoot { GOVERNANCE_ROOT_SLOT })` gate; driven
    // without a governance-membership witness it fails CLOSED — no membership proof,
    // no standing move. A bare self-write can never present a governance member's
    // proof, so it is refused exactly here.
    let program = guard_program();
    let old = base_state(2, 3, STANDING_GOOD);
    let mut new = old.clone();
    new.fields[STANDING_SLOT as usize] = field_from_u64(STANDING_SUSPENDED);
    let err = program
        .evaluate_with_meta(&new, Some(&old), None, &set_standing_meta())
        .expect_err("set_standing without a membership witness must be refused");
    match err {
        ProgramError::SenderMembershipWitnessMissing
        | ProgramError::WitnessedPredicateRequiresExecutor { .. }
        | ProgramError::MissingContextField { .. } => {} // any of these is a hard reject
        other => panic!("expected SenderMembershipWitnessMissing or similar, got {other:?}"),
    }
}

#[test]
fn set_standing_slot_shape_passes_when_authorized() {
    // With the sender gate stripped (the authorized-governance case), the `set_standing`
    // slot shape is well-formed: a good → suspended flip that leaves `consumed`,
    // `ceiling`, and the constitution untouched passes the slot-caveat layer. This is
    // the ACCEPT half the real witnessed executor path exercises in
    // `tests/governance_executor.rs`.
    let program = program_without_sender_authorized();
    let old = base_state(2, 3, STANDING_GOOD);
    let mut new = old.clone();
    new.fields[STANDING_SLOT as usize] = field_from_u64(STANDING_SUSPENDED);
    let r = program.evaluate_with_meta(&new, Some(&old), None, &set_standing_meta());
    assert!(
        r.is_ok(),
        "an authorized standing flip must pass the slot shape: {r:?}"
    );
}

#[test]
fn set_standing_cannot_fabricate_quota() {
    // A governance standing turn is not a quota refund: the `set_standing` case freezes
    // `consumed` (`Immutable`), so a takedown that also forges the meter down to zero is
    // refused. (Sender gate stripped to isolate the `Immutable(consumed)` tooth.)
    let program = program_without_sender_authorized();
    let old = base_state(2, 3, STANDING_GOOD);
    let mut bad_new = old.clone();
    bad_new.fields[STANDING_SLOT as usize] = field_from_u64(STANDING_SUSPENDED);
    bad_new.fields[CONSUMED_SLOT as usize] = field_from_u64(0); // forged down
    let err = program
        .evaluate_with_meta(&bad_new, Some(&old), None, &set_standing_meta())
        .expect_err("a standing turn that fabricates quota must be refused by Immutable");
    let msg = format!("{err:?}").to_lowercase();
    assert!(
        msg.contains("immutable") || msg.contains("constraint"),
        "refusal must cite the frozen consumed counter, got: {msg}"
    );
}

// ─── 3. Default-deny on an unknown method ────────────────────────────────

#[test]
fn an_unknown_method_that_touches_standing_is_default_denied() {
    // The `Cases` program defines dispatch cases (`consume_quota`, `set_standing`), so
    // an action whose method matches NONE of them is rejected outright (Cav-Codex Block
    // 4 default-deny) — even one that would otherwise satisfy the `Always` invariants.
    // The standing slot can never be touched by an unrecognized method.
    let program = guard_program();
    let old = base_state(0, 3, STANDING_GOOD);
    let mut new = old.clone();
    new.fields[STANDING_SLOT as usize] = field_from_u64(STANDING_SUSPENDED);
    let err = program
        .evaluate_with_meta(
            &new,
            Some(&old),
            None,
            &TransitionMeta::new(symbol("drain_all"), 0),
        )
        .expect_err("an unknown method must be default-denied");
    assert!(
        matches!(err, ProgramError::NoTransitionCaseMatched),
        "expected NoTransitionCaseMatched (default-deny), got {err:?}"
    );
}
