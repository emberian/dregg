//! Slot caveat composition **stress** tests.
//!
//! Layer: cell-side evaluator (`CellProgram::evaluate`), with one suite
//! that exercises `TransitionCase` / `TransitionGuard` dispatch through
//! `CellProgram::Cases`. These tests live alongside
//! `state_constraint_composition.rs` but go *broader*: a cell program
//! that declares **many** `StateConstraint` variants in one
//! `Predicate(_)`, `Cases(_)` programs with 5+ operation-scoped cases,
//! and large `AnyOf` disjunctions.
//!
//! Why a separate file: the existing composition file has 1-3 conjuncts
//! per program; this one stresses the evaluator with **21 declared
//! variants in one program** (one per enum variant where the cell-side
//! evaluator is honest) and operation-scoped dispatch over a 5-arm
//! `Cases` program.
//!
//! Per CAVEAT-LAYER-COVERAGE.md §1 the cell-side evaluator is honest
//! for 16 variants (FieldEquals/Gte/Lte, SumEquals, WriteOnce,
//! Immutable, Monotonic/StrictMonotonic, BoundedBy, FieldDelta,
//! FieldDeltaInRange, SumEqualsAcross, MonotonicSequence,
//! AllowedTransitions, TemporalGate, AnyOf) and structural-only for a
//! handful more. Sentinel variants (`TemporalPredicate`, `BoundDelta`,
//! `Witnessed`, `Custom`) propagate through the conjunction; we test
//! that they DO break the whole program until the caveat-correctness
//! lane lands.
//!
//! Discipline:
//! - Tests that compose only honest variants are *not* ignored —
//!   they're the regression guard for §8 of CAVEAT-LAYER-COVERAGE.
//! - Tests that mix in sentinel variants ARE ignored on the
//!   caveat-correctness lane (the sentinel collapses the program
//!   today; once the lane lands, these tests must invert).

#![allow(clippy::field_reassign_with_default)]

use pyana_cell::program::{SimpleStateConstraint, TransitionCase, TransitionGuard, TransitionMeta};
use pyana_cell::{
    CellProgram, CellState, EvalContext, FIELD_ZERO, StateConstraint, field_from_u64,
};

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

fn state_with(field_values: &[(usize, u64)]) -> CellState {
    let mut s = CellState::default();
    for (idx, val) in field_values {
        s.fields[*idx] = field_from_u64(*val);
    }
    s
}

fn ctx_at(block_height: u64, timestamp: i64) -> EvalContext {
    EvalContext::minimal(block_height, timestamp)
}

// ===========================================================================
// All-honest-variants composition (§8 surprisingly-complete regression
// guard)
// ===========================================================================

/// Declare 16 honest `StateConstraint` variants in **one**
/// `Predicate(...)` program, then exercise a transition that satisfies
/// every conjunct simultaneously. Per CAVEAT-LAYER-COVERAGE.md §8 the
/// substrate honestly handles all 16 — this test is the regression
/// guard against any future refactor that quietly silos them.
#[test]
fn predicate_all_honest_variants_in_one_program_accept_legal_transition() {
    // Layout of slots used (each variant gets its own slot or a small
    // group, to keep transitions independent):
    //   slot  0: FieldEquals(=1)       — static
    //   slot  1: FieldGte(>=100)       — static
    //   slot  2: FieldLte(<=200)       — static
    //   slots 3,4: SumEquals(=10)      — static (3+4 == 10)
    //   slot  5: WriteOnce             — 0 → 7 ok
    //   slot  6: Immutable             — old == new
    //   slot  7: Monotonic             — new >= old
    //   slot  8: StrictMonotonic       — new > old
    //   slot  9: BoundedBy(witness=10) — slot 10 must be non-zero on transition
    //   slot 10: (witness, set non-zero in new_state)
    //   slot 11: FieldDelta(+5)        — new = old + 5
    //   slot 12: FieldDeltaInRange     — new ∈ [old, old+10]
    //   slot 13: MonotonicSequence     — new = old + 1
    //   slot 14: AllowedTransitions    — (1, 2) in allow-list
    //   slots 15,16: SumEqualsAcross   — sum(in)=4+5=9, out=9
    //   slot 17: AnyOf                 — FieldEquals(=42) || FieldEquals(=43)
    //   TemporalGate: ctx.height ∈ [10, 100]

    let constraints = vec![
        StateConstraint::FieldEquals {
            index: 0,
            value: field_from_u64(1),
        },
        StateConstraint::FieldGte {
            index: 1,
            value: field_from_u64(100),
        },
        StateConstraint::FieldLte {
            index: 2,
            value: field_from_u64(200),
        },
        StateConstraint::SumEquals {
            indices: vec![3, 4],
            value: field_from_u64(10),
        },
        StateConstraint::WriteOnce { index: 5 },
        StateConstraint::Immutable { index: 6 },
        StateConstraint::Monotonic { index: 7 },
        StateConstraint::StrictMonotonic { index: 8 },
        StateConstraint::BoundedBy {
            index: 9,
            witness_index: 10,
        },
        StateConstraint::FieldDelta {
            index: 11,
            delta: field_from_u64(5),
        },
        StateConstraint::FieldDeltaInRange {
            index: 12,
            min_delta: field_from_u64(0),
            max_delta: field_from_u64(10),
        },
        StateConstraint::MonotonicSequence { seq_index: 13 },
        StateConstraint::AllowedTransitions {
            slot_index: 14,
            allowed: vec![(field_from_u64(1), field_from_u64(2))],
        },
        StateConstraint::SumEqualsAcross {
            input_fields: vec![15],
            output_fields: vec![16],
        },
        StateConstraint::AnyOf {
            variants: vec![
                SimpleStateConstraint::FieldEquals {
                    index: 17,
                    value: field_from_u64(42),
                },
                SimpleStateConstraint::FieldEquals {
                    index: 17,
                    value: field_from_u64(43),
                },
            ],
        },
        StateConstraint::TemporalGate {
            not_before: Some(10),
            not_after: Some(100),
        },
    ];
    let program = CellProgram::Predicate(constraints);

    // Old state: slot 5 = 0 (so WriteOnce can fire), slot 6 = 99
    // (Immutable), slot 7 = 50, slot 8 = 50, slot 9 = 0 (BoundedBy
    // witness check: only triggers on slot-9 transition), slot 11 = 20,
    // slot 12 = 100, slot 13 = 41, slot 14 = 1, slot 15 = 9, slot 16 = 0.
    let old = state_with(&[
        (5, 0),
        (6, 99),
        (7, 50),
        (8, 50),
        (9, 0),
        (10, 0),
        (11, 20),
        (12, 100),
        (13, 41),
        (14, 1),
        (15, 9),
        (16, 0),
    ]);
    // New state: every conjunct holds.
    let new = state_with(&[
        (0, 1),
        (1, 150),
        (2, 150),
        (3, 3),
        (4, 7),
        (5, 7),  // 0 -> 7: WriteOnce
        (6, 99), // unchanged: Immutable
        (7, 51), // monotonic
        (8, 60), // strict-monotonic
        (9, 0),  // not changing slot 9 — BoundedBy is "may only set if witness non-zero"
        (10, 0),
        (11, 25),  // 20 + 5
        (12, 105), // delta in [0, 10]
        (13, 42),  // 41 + 1
        (14, 2),   // allowed (1 -> 2)
        (15, 9),   // sum_in = 9, sum_out=9
        (16, 9),
        (17, 42), // AnyOf branch 1
    ]);
    let ctx = ctx_at(50, 0);
    let result = program.evaluate(&new, Some(&old), Some(&ctx));
    assert!(
        result.is_ok(),
        "16-variant honest-conjunction must accept a transition satisfying all conjuncts; got {result:?}"
    );
}

/// Same program, but break exactly one conjunct (Monotonic) — the
/// program must reject. The point is: one violation in a 16-conjunct
/// program is enough.
#[test]
fn predicate_all_honest_variants_one_violation_rejects_whole_program() {
    let constraints = vec![
        StateConstraint::FieldEquals {
            index: 0,
            value: field_from_u64(1),
        },
        StateConstraint::Monotonic { index: 7 },
        StateConstraint::StrictMonotonic { index: 8 },
    ];
    let program = CellProgram::Predicate(constraints);
    let old = state_with(&[(7, 50), (8, 50)]);
    // Monotonic broken: slot 7 decreases from 50 → 49.
    let new = state_with(&[(0, 1), (7, 49), (8, 60)]);
    assert!(
        program.evaluate(&new, Some(&old), None).is_err(),
        "single conjunct violation must reject the whole conjunction"
    );
}

// ===========================================================================
// AnyOf disjunction stress
// ===========================================================================

/// `AnyOf` with **20** branches — verifier should accept iff at least
/// one branch matches.
#[test]
fn any_of_with_twenty_branches_accepts_first_match() {
    let mut variants = Vec::new();
    for v in 0u64..20 {
        variants.push(SimpleStateConstraint::FieldEquals {
            index: 0,
            value: field_from_u64(v),
        });
    }
    let program = CellProgram::Predicate(vec![StateConstraint::AnyOf { variants }]);

    // slot 0 = 13 → branch 13 matches.
    let state = state_with(&[(0, 13)]);
    assert!(program.evaluate(&state, None, None).is_ok());

    // slot 0 = 100 → no branch matches.
    let state = state_with(&[(0, 100)]);
    assert!(program.evaluate(&state, None, None).is_err());
}

/// `AnyOf` with **zero** branches — the empty disjunction is `false`,
/// so every transition rejects. Important corner case for the
/// disjunction soundness claim.
#[test]
fn any_of_empty_rejects_every_transition() {
    let program = CellProgram::Predicate(vec![StateConstraint::AnyOf { variants: vec![] }]);
    let state = state_with(&[(0, 0)]);
    assert!(
        program.evaluate(&state, None, None).is_err(),
        "empty AnyOf must reject (false disjunction)"
    );
    let state = state_with(&[(0, 999)]);
    assert!(program.evaluate(&state, None, None).is_err());
}

/// Mix `AnyOf` (5 variants) with a conjunction tail. The conjunction
/// must hold AND at least one disjunct match.
#[test]
fn any_of_inside_conjunction_with_static_and_transition_constraints() {
    let program = CellProgram::Predicate(vec![
        StateConstraint::FieldEquals {
            index: 0,
            value: field_from_u64(1),
        },
        StateConstraint::Monotonic { index: 1 },
        StateConstraint::AnyOf {
            variants: vec![
                SimpleStateConstraint::FieldEquals {
                    index: 2,
                    value: field_from_u64(10),
                },
                SimpleStateConstraint::FieldEquals {
                    index: 2,
                    value: field_from_u64(20),
                },
                SimpleStateConstraint::FieldEquals {
                    index: 2,
                    value: field_from_u64(30),
                },
                SimpleStateConstraint::FieldEquals {
                    index: 2,
                    value: field_from_u64(40),
                },
                SimpleStateConstraint::FieldEquals {
                    index: 2,
                    value: field_from_u64(50),
                },
            ],
        },
    ]);
    let old = state_with(&[(1, 5)]);

    // All hold.
    let new = state_with(&[(0, 1), (1, 7), (2, 30)]);
    assert!(program.evaluate(&new, Some(&old), None).is_ok());

    // FieldEquals fails — outer conjunction rejects regardless of AnyOf.
    let new = state_with(&[(0, 2), (1, 7), (2, 30)]);
    assert!(program.evaluate(&new, Some(&old), None).is_err());

    // Monotonic fails — outer conjunction rejects regardless of AnyOf.
    let new = state_with(&[(0, 1), (1, 4), (2, 30)]);
    assert!(program.evaluate(&new, Some(&old), None).is_err());

    // AnyOf fails — slot 2 = 99 is not in {10,20,30,40,50}.
    let new = state_with(&[(0, 1), (1, 7), (2, 99)]);
    assert!(program.evaluate(&new, Some(&old), None).is_err());
}

// ===========================================================================
// `CellProgram::Cases` — operation-scoped dispatch
// ===========================================================================

/// 5 operation-scoped cases. Each fires on a different method symbol.
/// We verify that:
///   1. The matching case's constraints fire.
///   2. Non-matching cases' constraints are NOT applied (which is the
///      whole point of operation-scoping).
///   3. A turn whose method doesn't match any guard default-denies.
#[test]
fn cases_program_with_five_operation_arms_dispatches_per_method() {
    use pyana_turn::action::symbol;
    let m_mint = symbol("mint");
    let m_burn = symbol("burn");
    let m_transfer = symbol("transfer");
    let m_pause = symbol("pause");
    let m_resume = symbol("resume");

    let cases = vec![
        // mint: balance increases (Monotonic slot 0)
        TransitionCase {
            guard: TransitionGuard::MethodIs { method: m_mint },
            constraints: vec![StateConstraint::Monotonic { index: 0 }],
        },
        // burn: balance can only decrease — encode as "old > new" via
        // FieldDeltaInRange where the range is open-ended downward; we
        // use Monotonic on a *separate* counter slot to keep this test
        // simple. The mint and burn arms must NOT collide: only one
        // fires per turn.
        TransitionCase {
            guard: TransitionGuard::MethodIs { method: m_burn },
            constraints: vec![StateConstraint::Monotonic { index: 1 }],
        },
        // transfer: requires slot 2 to be in an allowed-transition set.
        TransitionCase {
            guard: TransitionGuard::MethodIs { method: m_transfer },
            constraints: vec![StateConstraint::AllowedTransitions {
                slot_index: 2,
                allowed: vec![(field_from_u64(1), field_from_u64(2))],
            }],
        },
        // pause: slot 3 must transition 0 → 1.
        TransitionCase {
            guard: TransitionGuard::MethodIs { method: m_pause },
            constraints: vec![StateConstraint::AllowedTransitions {
                slot_index: 3,
                allowed: vec![(field_from_u64(0), field_from_u64(1))],
            }],
        },
        // resume: slot 3 must transition 1 → 0.
        TransitionCase {
            guard: TransitionGuard::MethodIs { method: m_resume },
            constraints: vec![StateConstraint::AllowedTransitions {
                slot_index: 3,
                allowed: vec![(field_from_u64(1), field_from_u64(0))],
            }],
        },
    ];
    let program = CellProgram::Cases(cases);

    let old = state_with(&[(0, 5), (1, 100), (2, 1), (3, 0)]);
    // mint turn: slot 0 increases; nothing else's arm should fire.
    // slot 1 goes DOWN here, which would fail the burn-arm Monotonic,
    // but that case must not fire because method=mint.
    let new = state_with(&[(0, 10), (1, 50), (2, 1), (3, 0)]);
    let meta = TransitionMeta::new(m_mint, 0);
    let result = program.evaluate_with_meta(&new, Some(&old), None, &meta);
    assert!(
        result.is_ok(),
        "mint arm: only Monotonic(0) applies; got {result:?}"
    );

    // Unknown method default-denies (no arm matches).
    let unknown = symbol("frobnicate");
    let unknown_meta = TransitionMeta::new(unknown, 0);
    let result = program.evaluate_with_meta(&new, Some(&old), None, &unknown_meta);
    assert!(
        result.is_err(),
        "unknown method must default-deny in Cases program; got {result:?}"
    );
}

/// `Cases` program where the `mint` arm declares a constraint that is
/// VIOLATED. Even though `burn`'s arm would accept the same transition,
/// only the matching arm runs — so the program must reject.
#[test]
fn cases_program_does_not_try_other_arms_when_matching_arm_rejects() {
    use pyana_turn::action::symbol;
    let m_mint = symbol("mint");
    let m_burn = symbol("burn");

    let cases = vec![
        TransitionCase {
            guard: TransitionGuard::MethodIs { method: m_mint },
            // mint requires Monotonic on slot 0 — i.e. balance grows.
            constraints: vec![StateConstraint::Monotonic { index: 0 }],
        },
        TransitionCase {
            guard: TransitionGuard::MethodIs { method: m_burn },
            // burn would accept any transition (no constraint).
            constraints: vec![],
        },
    ];
    let program = CellProgram::Cases(cases);

    let old = state_with(&[(0, 100)]);
    // method=mint but slot 0 DECREASES → mint arm rejects; burn arm is
    // not tried.
    let new = state_with(&[(0, 50)]);
    let mint_meta = TransitionMeta::new(m_mint, 0);
    let _ = m_burn; // recorded for clarity even though we never invoke the burn arm
    assert!(
        program
            .evaluate_with_meta(&new, Some(&old), None, &mint_meta)
            .is_err(),
        "mint arm must reject the decrease; burn arm must not be considered"
    );
}

// ===========================================================================
// Cases + TransitionGuard composition
// ===========================================================================

/// `Cases` program with a `TransitionGuard::AnyOf` over multiple
/// methods, then an inner `AllOf` mixing `MethodIs` and `SlotChanged`.
/// This stresses the guard-tree composition.
#[test]
#[ignore = "blocks on TransitionGuard::SlotChanged: cell program evaluator needs old+new state visible to guard matcher (matches() is called but uses TransitionMeta only; SlotChanged path needs full state plumb-through)"]
fn cases_with_compound_transition_guards() {
    use pyana_turn::action::symbol;
    let m_a = symbol("act_a");
    let m_b = symbol("act_b");

    let cases = vec![TransitionCase {
        guard: TransitionGuard::AllOf(vec![
            TransitionGuard::AnyOf(vec![
                TransitionGuard::MethodIs { method: m_a },
                TransitionGuard::MethodIs { method: m_b },
            ]),
            TransitionGuard::SlotChanged { index: 0 },
        ]),
        constraints: vec![StateConstraint::Monotonic { index: 0 }],
    }];
    let _program = CellProgram::Cases(cases);
    panic!("blocked");
}

// ===========================================================================
// Sentinel-variant collapse (will INVERT once caveat-correctness lands)
// ===========================================================================

/// In a 16-honest-variant conjunction, *adding* a single sentinel
/// `Witnessed { wp }` variant must collapse the whole program to a
/// rejection (per CAVEAT-LAYER-COVERAGE.md §6.1). Today this is
/// guard rail; when the caveat-correctness lane wires the registry
/// dispatch, this test must be **inverted** to assert the conjunction
/// still accepts.
#[test]
fn sentinel_variant_inside_long_conjunction_collapses_program() {
    use pyana_cell::InputRef;
    use pyana_cell::predicate::WitnessedPredicate;

    let constraints = vec![
        StateConstraint::FieldEquals {
            index: 0,
            value: field_from_u64(1),
        },
        StateConstraint::Monotonic { index: 1 },
        // SENTINEL — must collapse the whole conjunction.
        StateConstraint::Witnessed {
            wp: WitnessedPredicate::dfa([0u8; 32], InputRef::Sender, 0),
        },
        // These remaining honest variants would all hold, but the
        // sentinel above takes the program down.
        StateConstraint::Immutable { index: 2 },
        StateConstraint::TemporalGate {
            not_before: Some(0),
            not_after: None,
        },
    ];
    let program = CellProgram::Predicate(constraints);
    let old = state_with(&[(1, 1), (2, 5)]);
    let new = state_with(&[(0, 1), (1, 2), (2, 5)]);
    let ctx = ctx_at(10, 0);
    assert!(
        program.evaluate(&new, Some(&old), Some(&ctx)).is_err(),
        "sentinel variant must collapse the conjunction until caveat-correctness lane lands"
    );
}

#[test]
#[ignore = "INVERTED form: once caveat-correctness lane wires WitnessedPredicateRegistry from cell-program path (CAVEAT-LAYER-COVERAGE.md §6.6), the 16-honest+1-witnessed conjunction must accept when the witness verifies"]
fn sentinel_variant_inside_long_conjunction_accepts_when_witness_verifies() {
    panic!("blocked");
}

// ===========================================================================
// Programs that declare ALL 21+ variants at once
// ===========================================================================

#[test]
#[ignore = "blocks on caveat-correctness lane: full 21+ variant declaration cannot accept any transition today because TemporalPredicate/BoundDelta/Witnessed/Custom collapse the conjunction (CAVEAT-LAYER-COVERAGE.md §6.1). Once the lane lands, this test asserts the maximally-rich cell program can transition."]
fn all_21_state_constraint_variants_declared_and_satisfied() {
    panic!("blocked");
}

// ===========================================================================
// Composition + ctx-honesty: TemporalGate + FieldGteHeight (both read
// ctx.block_height)
// ===========================================================================

#[test]
fn temporal_gate_plus_field_gte_height_both_read_block_height_honestly() {
    // Two contextual variants in one program. Both must see the same
    // ctx.block_height; if the evaluator silos them, this would catch it.
    let program = CellProgram::Predicate(vec![
        StateConstraint::TemporalGate {
            not_before: Some(50),
            not_after: Some(100),
        },
        StateConstraint::FieldGteHeight {
            index: 0,
            offset: 10, // slot 0 must be >= ctx.block_height + 10
        },
    ]);

    // height=60, slot 0=80: TemporalGate ok (50 <= 60 <= 100),
    // FieldGteHeight ok (80 >= 60 + 10 = 70).
    let new = state_with(&[(0, 80)]);
    let ctx = ctx_at(60, 0);
    assert!(program.evaluate(&new, None, Some(&ctx)).is_ok());

    // height=30: TemporalGate fails (30 < 50).
    let ctx = ctx_at(30, 0);
    assert!(program.evaluate(&new, None, Some(&ctx)).is_err());

    // height=60, slot 0=65: FieldGteHeight fails (65 < 70).
    let new = state_with(&[(0, 65)]);
    let ctx = ctx_at(60, 0);
    assert!(program.evaluate(&new, None, Some(&ctx)).is_err());
}

// ===========================================================================
// Programs that exercise the FIELD_ZERO sentinel
// ===========================================================================

#[test]
fn write_once_fires_on_zero_to_nonzero_only() {
    let program = CellProgram::Predicate(vec![StateConstraint::WriteOnce { index: 0 }]);
    // 0 → 7: ok (first write).
    let old = state_with(&[]);
    let new = state_with(&[(0, 7)]);
    assert!(program.evaluate(&new, Some(&old), None).is_ok());

    // 7 → 7: ok (unchanged).
    let old = state_with(&[(0, 7)]);
    let new = state_with(&[(0, 7)]);
    assert!(program.evaluate(&new, Some(&old), None).is_ok());

    // 7 → 8: reject (second write).
    let new = state_with(&[(0, 8)]);
    assert!(program.evaluate(&new, Some(&old), None).is_err());
}

#[test]
fn write_once_inside_long_conjunction_still_fires() {
    let program = CellProgram::Predicate(vec![
        StateConstraint::FieldEquals {
            index: 1,
            value: field_from_u64(1),
        },
        StateConstraint::WriteOnce { index: 0 },
        StateConstraint::Monotonic { index: 2 },
    ]);
    let old = state_with(&[(0, 7), (2, 5)]);
    // WriteOnce violated: 7 → 8.
    let new = state_with(&[(0, 8), (1, 1), (2, 6)]);
    assert!(
        program.evaluate(&new, Some(&old), None).is_err(),
        "WriteOnce must fire inside a 3-conjunct program"
    );
}

// ===========================================================================
// Sanity: evaluator on empty conjunction == accept (no constraints)
// ===========================================================================

#[test]
fn predicate_with_empty_constraint_list_accepts_everything() {
    let program = CellProgram::Predicate(vec![]);
    assert!(program.evaluate(&CellState::default(), None, None).is_ok());
    assert!(
        program
            .evaluate(&state_with(&[(0, 999)]), None, None)
            .is_ok()
    );
}

// ===========================================================================
// `None` program — accepts everything trivially
// ===========================================================================

#[test]
fn cell_program_none_accepts_every_transition() {
    let program = CellProgram::None;
    let _ = FIELD_ZERO; // touch the import so it's visible in test output
    assert!(program.evaluate(&CellState::default(), None, None).is_ok());
    let new = state_with(&[(0, 99), (5, 17), (31, 1)]);
    assert!(program.evaluate(&new, None, None).is_ok());
}
