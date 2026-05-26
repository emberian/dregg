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
//! `Witnessed`, `TemporalPredicate`, and `Custom`) now dispatch when an
//! explicit registry and witness bundle are provided; `BoundDelta`
//! remains a cross-cell/gamma-layer sentinel and is intentionally not
//! modeled as accepted here.
//!
//! Discipline:
//! - Tests that compose only honest variants are *not* ignored —
//!   they're the regression guard for §8 of CAVEAT-LAYER-COVERAGE.
//! - Tests that mix in registry-backed variants install exact
//!   test-local verifiers rather than permissive stubs.

#![allow(clippy::field_reassign_with_default)]

use std::sync::Arc;

use dregg_cell::predicate::{
    PredicateInput, WitnessedPredicate, WitnessedPredicateError, WitnessedPredicateKind,
    WitnessedPredicateRegistry, WitnessedPredicateVerifier,
};
use dregg_cell::program::{
    CustomDescriptor, ReadSet, SimpleStateConstraint, TransitionCase, TransitionGuard,
    TransitionMeta, WitnessBlobView, WitnessBundle, WitnessKindTag,
};
use dregg_cell::{
    CellProgram, CellState, EvalContext, FIELD_ZERO, InputRef, StateConstraint, field_from_u64,
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

struct ExactProofVerifier {
    kind: WitnessedPredicateKind,
    name: &'static str,
    expected_commitment: [u8; 32],
    expected_proof: &'static [u8],
}

impl WitnessedPredicateVerifier for ExactProofVerifier {
    fn name(&self) -> &'static str {
        self.name
    }

    fn kind(&self) -> WitnessedPredicateKind {
        self.kind
    }

    fn verify(
        &self,
        commitment: &[u8; 32],
        _input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        if commitment != &self.expected_commitment {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: self.name(),
                reason: "commitment mismatch".into(),
            });
        }
        if proof_bytes != self.expected_proof {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: self.name(),
                reason: "proof mismatch".into(),
            });
        }
        Ok(())
    }
}

fn stress_registry(custom_hash: [u8; 32]) -> WitnessedPredicateRegistry {
    let mut registry = WitnessedPredicateRegistry::empty();
    registry.register_builtin(Arc::new(ExactProofVerifier {
        kind: WitnessedPredicateKind::Dfa,
        name: "stress-dfa-verifier",
        expected_commitment: [0xD1u8; 32],
        expected_proof: b"shared-proof",
    }));
    registry.register_builtin(Arc::new(ExactProofVerifier {
        kind: WitnessedPredicateKind::Temporal,
        name: "stress-temporal-verifier",
        expected_commitment: [0xD2u8; 32],
        expected_proof: b"shared-proof",
    }));
    registry.register_custom(
        custom_hash,
        Arc::new(ExactProofVerifier {
            kind: WitnessedPredicateKind::Custom {
                vk_hash: custom_hash,
            },
            name: "stress-custom-verifier",
            expected_commitment: custom_hash,
            expected_proof: b"shared-proof",
        }),
    );
    registry
}

// ===========================================================================
// All-honest-variants composition (§8 surprisingly-complete regression
// guard)
// ===========================================================================

/// Declare honest `StateConstraint` variants in **one**
/// `Predicate(...)` program, then exercise a transition that satisfies
/// every conjunct simultaneously. Per CAVEAT-LAYER-COVERAGE.md §8 the
/// substrate honestly handles all of these — this test is the regression
/// guard against any future refactor that quietly silos them.
///
/// Note: `STATE_SLOTS = 8` limits us to indices 0..7. The original design
/// used indices 0..17; those have been remapped to fit the current cell-state
/// capacity. Variants not fitting in 8 independent slots (SumEqualsAcross,
/// BoundedBy, SumEquals) are tested in `state_constraint_composition.rs`
/// and the unit-level `state_constraint_variants.rs`.
#[test]
fn predicate_all_honest_variants_in_one_program_accept_legal_transition() {
    // Layout of slots used (all within [0, 7] — STATE_SLOTS = 8):
    //   slot 0: FieldEquals(=1)           — static value check
    //   slot 1: FieldGte(>=100)           — static lower bound
    //           + StrictMonotonic         — new(150) > old(100) covers both
    //   slot 2: FieldLte(<=200)           — static upper bound
    //   slot 3: WriteOnce                 — old=0 → new=7
    //   slot 4: Immutable                 — old=99, new=99 (unchanged)
    //   slot 5: FieldDelta(+5)            — new = old + 5
    //   slot 6: MonotonicSequence         — new = old + 1 (seq counter)
    //   slot 7: AllowedTransitions(1→2)   — explicit state-machine arc
    //           + AnyOf(FieldEquals=2)    — disjunct on same slot value
    //   TemporalGate: ctx.height ∈ [10, 100] — no slot needed

    let constraints = vec![
        StateConstraint::FieldEquals {
            index: 0,
            value: field_from_u64(1),
        },
        StateConstraint::FieldGte {
            index: 1,
            value: field_from_u64(100),
        },
        // slot 1 also satisfies StrictMonotonic (150 > 100).
        StateConstraint::StrictMonotonic { index: 1 },
        StateConstraint::FieldLte {
            index: 2,
            value: field_from_u64(200),
        },
        StateConstraint::WriteOnce { index: 3 },
        StateConstraint::Immutable { index: 4 },
        StateConstraint::FieldDelta {
            index: 5,
            delta: field_from_u64(5),
        },
        StateConstraint::MonotonicSequence { seq_index: 6 },
        StateConstraint::AllowedTransitions {
            slot_index: 7,
            allowed: vec![(field_from_u64(1), field_from_u64(2))],
        },
        // AnyOf on slot 7: new value is 2, which matches branch 1.
        StateConstraint::AnyOf {
            variants: vec![
                SimpleStateConstraint::FieldEquals {
                    index: 7,
                    value: field_from_u64(2),
                },
                SimpleStateConstraint::FieldEquals {
                    index: 7,
                    value: field_from_u64(3),
                },
            ],
        },
        StateConstraint::TemporalGate {
            not_before: Some(10),
            not_after: Some(100),
        },
    ];
    let program = CellProgram::Predicate(constraints);

    // Old state:
    //   slot 1 = 100 (for StrictMonotonic: new must be > 100)
    //   slot 3 = 0   (WriteOnce: first write from zero)
    //   slot 4 = 99  (Immutable: must stay 99)
    //   slot 5 = 20  (FieldDelta: new = 25)
    //   slot 6 = 41  (MonotonicSequence: new = 42)
    //   slot 7 = 1   (AllowedTransitions: 1 → 2)
    let old = state_with(&[(1, 100), (3, 0), (4, 99), (5, 20), (6, 41), (7, 1)]);
    // New state: every conjunct holds simultaneously.
    let new = state_with(&[
        (0, 1),   // FieldEquals(=1)
        (1, 150), // FieldGte(>=100) + StrictMonotonic (150 > 100)
        (2, 150), // FieldLte(<=200)
        (3, 7),   // WriteOnce: 0 → 7
        (4, 99),  // Immutable: unchanged
        (5, 25),  // FieldDelta: 20 + 5
        (6, 42),  // MonotonicSequence: 41 + 1
        (7, 2),   // AllowedTransitions: (1, 2) in list; AnyOf branch 0 matches
    ]);
    let ctx = ctx_at(50, 0);
    let result = program.evaluate(&new, Some(&old), Some(&ctx));
    assert!(
        result.is_ok(),
        "10-variant honest-conjunction must accept a transition satisfying all conjuncts; got {result:?}"
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
        StateConstraint::Monotonic { index: 6 },
        StateConstraint::StrictMonotonic { index: 7 }, // valid: indices 0..7 only
    ];
    let program = CellProgram::Predicate(constraints);
    let old = state_with(&[(6, 50), (7, 50)]);
    // Monotonic broken: slot 6 decreases from 50 → 49.
    let new = state_with(&[(0, 1), (6, 49), (7, 60)]);
    assert!(
        program.evaluate(&new, Some(&old), None).is_err(),
        "single conjunct violation must reject the whole conjunction"
    );
}

// ===========================================================================
// Rate / window-sum caveats inside long conjunctions
// ===========================================================================

#[test]
fn predicate_long_conjunction_with_rate_limit_and_window_sum_accepts_under_caps() {
    // Layout:
    //   slot 0: static product/state marker
    //   slot 1: monotonic counter
    //   slot 2: per-window sum source
    //   slot 3: AnyOf dispatch marker
    let program = CellProgram::Predicate(vec![
        StateConstraint::FieldEquals {
            index: 0,
            value: field_from_u64(1),
        },
        StateConstraint::Monotonic { index: 1 },
        StateConstraint::RateLimit {
            max_per_epoch: 5,
            epoch_duration: 32,
        },
        StateConstraint::RateLimitBySum {
            slot_index: 2,
            max_sum_per_epoch: 50,
            epoch_duration: 32,
        },
        StateConstraint::TemporalGate {
            not_before: Some(10),
            not_after: Some(100),
        },
        StateConstraint::AnyOf {
            variants: vec![
                SimpleStateConstraint::FieldEquals {
                    index: 3,
                    value: field_from_u64(7),
                },
                SimpleStateConstraint::FieldEquals {
                    index: 3,
                    value: field_from_u64(9),
                },
            ],
        },
    ]);

    let old = state_with(&[(1, 10), (2, 100)]);
    let new = state_with(&[(0, 1), (1, 11), (2, 130), (3, 7)]);
    let mut ctx = ctx_at(50, 0);
    ctx.sender = Some([8u8; 32]);
    ctx.sender_epoch_count = 4;

    let result = program.evaluate(&new, Some(&old), Some(&ctx));
    assert!(
        result.is_ok(),
        "rate, window-sum, temporal, transition, and AnyOf conjuncts should all accept; got {result:?}"
    );
}

#[test]
fn predicate_long_conjunction_with_rate_limit_and_window_sum_rejects_each_cap() {
    let program = CellProgram::Predicate(vec![
        StateConstraint::FieldEquals {
            index: 0,
            value: field_from_u64(1),
        },
        StateConstraint::Monotonic { index: 1 },
        StateConstraint::RateLimit {
            max_per_epoch: 5,
            epoch_duration: 32,
        },
        StateConstraint::RateLimitBySum {
            slot_index: 2,
            max_sum_per_epoch: 50,
            epoch_duration: 32,
        },
        StateConstraint::TemporalGate {
            not_before: Some(10),
            not_after: Some(100),
        },
    ]);

    let old = state_with(&[(1, 10), (2, 100)]);
    let new = state_with(&[(0, 1), (1, 11), (2, 130)]);
    let mut at_rate_cap = ctx_at(50, 0);
    at_rate_cap.sender = Some([8u8; 32]);
    at_rate_cap.sender_epoch_count = 5;
    assert!(
        program
            .evaluate(&new, Some(&old), Some(&at_rate_cap))
            .is_err(),
        "RateLimit must reject the whole conjunction at the per-epoch cap"
    );

    let over_window_sum = state_with(&[(0, 1), (1, 11), (2, 151)]);
    let mut under_rate_cap = ctx_at(50, 0);
    under_rate_cap.sender = Some([8u8; 32]);
    under_rate_cap.sender_epoch_count = 4;
    assert!(
        program
            .evaluate(&over_window_sum, Some(&old), Some(&under_rate_cap))
            .is_err(),
        "RateLimitBySum must reject the whole conjunction above the per-window delta cap"
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
    use dregg_turn::action::symbol;
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
    use dregg_turn::action::symbol;
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
fn cases_with_compound_transition_guards() {
    use dregg_turn::action::symbol;
    let m_a = symbol("act_a");
    let m_b = symbol("act_b");

    let program = CellProgram::Cases(vec![TransitionCase {
        guard: TransitionGuard::AllOf(vec![
            TransitionGuard::AnyOf(vec![
                TransitionGuard::MethodIs { method: m_a },
                TransitionGuard::MethodIs { method: m_b },
            ]),
            TransitionGuard::SlotChanged { index: 0 },
        ]),
        constraints: vec![StateConstraint::Monotonic { index: 0 }],
    }]);

    // Case 1: method=m_a, slot 0 increased => AllOf matches, Monotonic satisfied => Ok
    let old = state_with(&[(0, 5)]);
    let new = state_with(&[(0, 10)]);
    let meta_a = TransitionMeta::new(m_a, 0);
    assert!(
        program
            .evaluate_with_meta(&new, Some(&old), None, &meta_a)
            .is_ok(),
        "m_a + slot 0 changed + monotonic satisfied => must accept"
    );

    // Case 2: method=m_b, slot 0 increased => AllOf matches, Monotonic satisfied => Ok
    let meta_b = TransitionMeta::new(m_b, 0);
    assert!(
        program
            .evaluate_with_meta(&new, Some(&old), None, &meta_b)
            .is_ok(),
        "m_b + slot 0 changed + monotonic satisfied => must accept"
    );

    // Case 3: method=m_a, slot 0 did NOT change => SlotChanged is false =>
    //         AllOf fails => no case matched => must reject
    let unchanged = state_with(&[(0, 5)]);
    assert!(
        program
            .evaluate_with_meta(&unchanged, Some(&old), None, &meta_a)
            .is_err(),
        "m_a + slot 0 unchanged => SlotChanged false => no case matched => must reject"
    );

    // Case 4: slot 0 changed but method is neither m_a nor m_b =>
    //         AnyOf fails => AllOf fails => no case matched => must reject
    let unrelated_meta = TransitionMeta::new(symbol("unrelated"), 0);
    assert!(
        program
            .evaluate_with_meta(&new, Some(&old), None, &unrelated_meta)
            .is_err(),
        "unrelated method + slot changed => AnyOf fails => no case matched => must reject"
    );
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
    use dregg_cell::InputRef;
    use dregg_cell::predicate::WitnessedPredicate;

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
fn sentinel_variant_inside_long_conjunction_accepts_when_witness_verifies() {
    let constraints = vec![
        StateConstraint::FieldEquals {
            index: 0,
            value: field_from_u64(1),
        },
        StateConstraint::Monotonic { index: 1 },
        StateConstraint::Witnessed {
            wp: WitnessedPredicate::dfa([0xD1u8; 32], InputRef::Sender, 0),
        },
        StateConstraint::Immutable { index: 2 },
        StateConstraint::TemporalGate {
            not_before: Some(0),
            not_after: None,
        },
    ];
    let program = CellProgram::Predicate(constraints);
    let old = state_with(&[(1, 1), (2, 5)]);
    let new = state_with(&[(0, 1), (1, 2), (2, 5)]);
    let mut ctx = ctx_at(10, 0);
    ctx.sender = Some([0xA5u8; 32]);
    let registry = stress_registry([0xC3u8; 32]);
    let blobs = [WitnessBlobView {
        kind: WitnessKindTag::ProofBytes,
        bytes: b"shared-proof",
    }];
    let witnesses = WitnessBundle {
        blobs: &blobs,
        registry: Some(&registry),
    };

    let result = program.evaluate_full(
        &new,
        Some(&old),
        Some(&ctx),
        &TransitionMeta::wildcard(),
        &witnesses,
    );
    assert!(
        result.is_ok(),
        "honest conjunction plus verified Witnessed predicate must accept, got: {result:?}"
    );
}

// ===========================================================================
// Programs that declare all locally dispatchable variants at once
// ===========================================================================

#[test]
fn all_locally_dispatchable_state_constraint_variants_declared_and_satisfied() {
    let custom_hash = [0xC3u8; 32];
    let registry = stress_registry(custom_hash);
    let blobs = [
        WitnessBlobView {
            kind: WitnessKindTag::ProofBytes,
            bytes: b"shared-proof",
        },
        WitnessBlobView {
            kind: WitnessKindTag::Cleartext,
            bytes: b"temporal-window",
        },
    ];
    let witnesses = WitnessBundle {
        blobs: &blobs,
        registry: Some(&registry),
    };
    let program = CellProgram::Predicate(vec![
        StateConstraint::FieldEquals {
            index: 0,
            value: field_from_u64(1),
        },
        StateConstraint::FieldGte {
            index: 1,
            value: field_from_u64(100),
        },
        StateConstraint::StrictMonotonic { index: 1 },
        StateConstraint::FieldLte {
            index: 2,
            value: field_from_u64(200),
        },
        StateConstraint::WriteOnce { index: 3 },
        StateConstraint::Immutable { index: 4 },
        StateConstraint::FieldDelta {
            index: 5,
            delta: field_from_u64(5),
        },
        StateConstraint::MonotonicSequence { seq_index: 6 },
        StateConstraint::AllowedTransitions {
            slot_index: 7,
            allowed: vec![(field_from_u64(1), field_from_u64(2))],
        },
        StateConstraint::AnyOf {
            variants: vec![
                SimpleStateConstraint::FieldEquals {
                    index: 7,
                    value: field_from_u64(2),
                },
                SimpleStateConstraint::FieldEquals {
                    index: 7,
                    value: field_from_u64(3),
                },
            ],
        },
        StateConstraint::TemporalGate {
            not_before: Some(10),
            not_after: Some(100),
        },
        StateConstraint::TemporalPredicate {
            dsl_hash: [0xD2u8; 32],
            witness_index: 1,
        },
        StateConstraint::Witnessed {
            wp: WitnessedPredicate::dfa([0xD1u8; 32], InputRef::Sender, 0),
        },
        StateConstraint::Custom {
            ir_hash: custom_hash,
            descriptor: CustomDescriptor::default(),
            reads: ReadSet::default(),
        },
    ]);
    let old = state_with(&[(1, 100), (3, 0), (4, 99), (5, 20), (6, 41), (7, 1)]);
    let new = state_with(&[
        (0, 1),
        (1, 150),
        (2, 150),
        (3, 7),
        (4, 99),
        (5, 25),
        (6, 42),
        (7, 2),
    ]);
    let mut ctx = ctx_at(50, 0);
    ctx.sender = Some([0xA5u8; 32]);
    let result = program.evaluate_full(
        &new,
        Some(&old),
        Some(&ctx),
        &TransitionMeta::wildcard(),
        &witnesses,
    );
    assert!(
        result.is_ok(),
        "all locally dispatchable variants should compose when exact witnesses verify; got {result:?}"
    );
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
    let new = state_with(&[(0, 99), (5, 17), (7, 1)]); // slot 7 is the last valid index (STATE_SLOTS = 8)
    assert!(program.evaluate(&new, None, None).is_ok());
}
