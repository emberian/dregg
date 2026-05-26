//! Atomic per-variant tests for every `StateConstraint` variant.
//!
//! Layer: **unit / cell-side evaluator**. Drives `CellProgram::evaluate_full`
//! directly with synthesised `(old_state, new_state, ctx, witnesses)` triples;
//! does NOT go through the executor. This layer answers the question:
//! "given an honest evaluator and a well-formed input, does each variant
//! accept the legal transition and reject the illegal one?"
//!
//! Companion files:
//! - `state_constraint_executor.rs` — same matrix, but through `TurnExecutor`
//!   (catches placeholder-context regressions documented in
//!   CAVEAT-LAYER-COVERAGE.md §6.2).
//! - `state_constraint_composition.rs` — multi-variant `Predicate(Vec<_>)`
//!   conjunction tests.
//!
//! Discipline:
//! - Each variant has at least a positive and a negative test.
//! - Tests that require executor-side context plumbing (e.g. `RateLimit`
//!   needs a per-(cell,sender,epoch) counter the cell-side evaluator does
//!   not see) are marked `#[ignore]` with a clear unblock-by-lane reason.
//! - Variants whose cell-side evaluator returns a sentinel today
//!   (`TemporalPredicate`, `BoundDelta`, `Witnessed`, `Custom`) get
//!   tests that assert the sentinel shape and a second `#[ignore]`d test
//!   asserting the eventual positive behaviour.

#![allow(clippy::field_reassign_with_default)]

use std::sync::Arc;

use dregg_cell::predicate::{
    PredicateInput, WitnessedPredicate, WitnessedPredicateError, WitnessedPredicateKind,
    WitnessedPredicateRegistry, WitnessedPredicateVerifier,
};
use dregg_cell::program::{
    AuthorizedSet, CustomDescriptor, DeltaRelation, HashKind, ReadSet, SimpleStateConstraint,
    TransitionCase, TransitionGuard, TransitionMeta, WitnessBlobView, WitnessBundle,
    WitnessKindTag,
};
use dregg_cell::{
    CellProgram, CellState, EFFECT_SET_FIELD, EvalContext, FIELD_ZERO, FieldElement, InputRef,
    ProgramError, StateConstraint, field_from_u64,
};
use dregg_turn::action::symbol;

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

fn state_raw_with(field_values: &[(usize, FieldElement)]) -> CellState {
    let mut s = CellState::default();
    for (idx, val) in field_values {
        s.fields[*idx] = *val;
    }
    s
}

/// Build a `Predicate(Vec<_>)` program out of a single constraint.
fn single_predicate(c: StateConstraint) -> CellProgram {
    CellProgram::Predicate(vec![c])
}

struct ExactSenderVerifier {
    kind: WitnessedPredicateKind,
    name: &'static str,
    expected_commitment: [u8; 32],
    expected_sender: [u8; 32],
    expected_proof: &'static [u8],
}

impl WitnessedPredicateVerifier for ExactSenderVerifier {
    fn name(&self) -> &'static str {
        self.name
    }

    fn kind(&self) -> WitnessedPredicateKind {
        self.kind
    }

    fn verify(
        &self,
        commitment: &[u8; 32],
        input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        if commitment != &self.expected_commitment {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: self.name(),
                reason: "commitment mismatch".into(),
            });
        }
        match input {
            PredicateInput::Sender(sender) if *sender == &self.expected_sender => {}
            PredicateInput::Sender(_) => {
                return Err(WitnessedPredicateError::Rejected {
                    kind_name: self.name(),
                    reason: "sender mismatch".into(),
                });
            }
            _ => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: self.name(),
                    expected: "Sender",
                    actual: "non-Sender",
                });
            }
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

fn exact_dfa_registry(
    expected_commitment: [u8; 32],
    expected_sender: [u8; 32],
    expected_proof: &'static [u8],
) -> WitnessedPredicateRegistry {
    let mut registry = WitnessedPredicateRegistry::empty();
    registry.register_builtin(Arc::new(ExactSenderVerifier {
        kind: WitnessedPredicateKind::Dfa,
        name: "exact-dfa-state-constraint-test-verifier",
        expected_commitment,
        expected_sender,
        expected_proof,
    }));
    registry
}

/// Assert that the program accepts the transition.
fn assert_accept(
    program: &CellProgram,
    new_state: &CellState,
    old_state: Option<&CellState>,
    ctx: Option<&EvalContext>,
    label: &str,
) {
    let res = program.evaluate(new_state, old_state, ctx);
    assert!(res.is_ok(), "[{label}] expected accept, got: {res:?}");
}

/// Assert the program rejects with a `ConstraintViolated` error.
fn assert_reject_violated(
    program: &CellProgram,
    new_state: &CellState,
    old_state: Option<&CellState>,
    ctx: Option<&EvalContext>,
    label: &str,
) {
    let res = program.evaluate(new_state, old_state, ctx);
    match res {
        Err(ProgramError::ConstraintViolated { .. }) => {}
        other => panic!("[{label}] expected ConstraintViolated, got: {other:?}"),
    }
}

/// Assert the program rejects with any error matching the predicate.
fn assert_reject_err<F: FnOnce(&ProgramError) -> bool>(
    program: &CellProgram,
    new_state: &CellState,
    old_state: Option<&CellState>,
    ctx: Option<&EvalContext>,
    pred: F,
    label: &str,
) {
    let res = program.evaluate(new_state, old_state, ctx);
    match res {
        Err(ref e) if pred(e) => {}
        other => panic!("[{label}] unexpected result: {other:?}"),
    }
}

// ===========================================================================
// 1. FieldEquals
// ===========================================================================

#[test]
fn field_equals_accepts_matching_value() {
    let p = single_predicate(StateConstraint::FieldEquals {
        index: 0,
        value: field_from_u64(42),
    });
    let new_state = state_with(&[(0, 42)]);
    assert_accept(&p, &new_state, None, None, "FieldEquals positive");
}

#[test]
fn field_equals_rejects_mismatching_value() {
    let p = single_predicate(StateConstraint::FieldEquals {
        index: 0,
        value: field_from_u64(42),
    });
    let new_state = state_with(&[(0, 41)]);
    assert_reject_violated(&p, &new_state, None, None, "FieldEquals negative");
}

#[test]
fn field_equals_rejects_invalid_index() {
    let p = single_predicate(StateConstraint::FieldEquals {
        index: 99,
        value: FIELD_ZERO,
    });
    let new_state = CellState::default();
    assert_reject_err(
        &p,
        &new_state,
        None,
        None,
        |e| matches!(e, ProgramError::InvalidFieldIndex { index: 99 }),
        "FieldEquals invalid index",
    );
}

// ===========================================================================
// 2. FieldGte
// ===========================================================================

#[test]
fn field_gte_accepts_equal_and_greater() {
    let p = single_predicate(StateConstraint::FieldGte {
        index: 0,
        value: field_from_u64(10),
    });
    assert_accept(&p, &state_with(&[(0, 10)]), None, None, "FieldGte equal");
    assert_accept(&p, &state_with(&[(0, 11)]), None, None, "FieldGte greater");
}

#[test]
fn field_gte_rejects_less_than() {
    let p = single_predicate(StateConstraint::FieldGte {
        index: 0,
        value: field_from_u64(10),
    });
    assert_reject_violated(&p, &state_with(&[(0, 9)]), None, None, "FieldGte negative");
}

// ===========================================================================
// 3. FieldLte
// ===========================================================================

#[test]
fn field_lte_accepts_equal_and_less() {
    let p = single_predicate(StateConstraint::FieldLte {
        index: 0,
        value: field_from_u64(10),
    });
    assert_accept(&p, &state_with(&[(0, 10)]), None, None, "FieldLte equal");
    assert_accept(&p, &state_with(&[(0, 9)]), None, None, "FieldLte less");
}

#[test]
fn field_lte_rejects_greater_than() {
    let p = single_predicate(StateConstraint::FieldLte {
        index: 0,
        value: field_from_u64(10),
    });
    assert_reject_violated(&p, &state_with(&[(0, 11)]), None, None, "FieldLte negative");
}

// ===========================================================================
// 4. SumEquals
// ===========================================================================

#[test]
fn sum_equals_accepts_correct_sum() {
    let p = single_predicate(StateConstraint::SumEquals {
        indices: vec![0, 1, 2],
        value: field_from_u64(60),
    });
    let new_state = state_with(&[(0, 10), (1, 20), (2, 30)]);
    assert_accept(&p, &new_state, None, None, "SumEquals positive");
}

#[test]
fn sum_equals_rejects_wrong_sum() {
    let p = single_predicate(StateConstraint::SumEquals {
        indices: vec![0, 1, 2],
        value: field_from_u64(60),
    });
    let new_state = state_with(&[(0, 10), (1, 20), (2, 25)]);
    assert_reject_violated(&p, &new_state, None, None, "SumEquals negative");
}

// ===========================================================================
// 5. WriteOnce
// ===========================================================================

#[test]
fn write_once_accepts_first_write_from_zero() {
    let p = single_predicate(StateConstraint::WriteOnce { index: 3 });
    let old = state_with(&[]);
    let new = state_with(&[(3, 7)]);
    assert_accept(&p, &new, Some(&old), None, "WriteOnce first write");
}

#[test]
fn write_once_accepts_unchanged_after_write() {
    let p = single_predicate(StateConstraint::WriteOnce { index: 3 });
    let old = state_with(&[(3, 7)]);
    let new = state_with(&[(3, 7)]);
    assert_accept(&p, &new, Some(&old), None, "WriteOnce unchanged");
}

#[test]
fn write_once_rejects_overwrite() {
    let p = single_predicate(StateConstraint::WriteOnce { index: 3 });
    let old = state_with(&[(3, 7)]);
    let new = state_with(&[(3, 9)]);
    assert_reject_violated(&p, &new, Some(&old), None, "WriteOnce overwrite");
}

// ===========================================================================
// 6. Immutable
// ===========================================================================

#[test]
fn immutable_accepts_unchanged() {
    let p = single_predicate(StateConstraint::Immutable { index: 2 });
    let old = state_with(&[(2, 5)]);
    let new = state_with(&[(2, 5)]);
    assert_accept(&p, &new, Some(&old), None, "Immutable unchanged");
}

#[test]
fn immutable_rejects_any_change() {
    let p = single_predicate(StateConstraint::Immutable { index: 2 });
    let old = state_with(&[(2, 5)]);
    let new = state_with(&[(2, 6)]);
    assert_reject_violated(&p, &new, Some(&old), None, "Immutable changed");
}

// ===========================================================================
// 7. Monotonic
// ===========================================================================

#[test]
fn monotonic_accepts_equal_and_increasing() {
    let p = single_predicate(StateConstraint::Monotonic { index: 1 });
    let old = state_with(&[(1, 5)]);
    assert_accept(&p, &state_with(&[(1, 5)]), Some(&old), None, "Monotonic eq");
    assert_accept(&p, &state_with(&[(1, 6)]), Some(&old), None, "Monotonic gt");
}

#[test]
fn monotonic_rejects_decreasing() {
    let p = single_predicate(StateConstraint::Monotonic { index: 1 });
    let old = state_with(&[(1, 5)]);
    let new = state_with(&[(1, 4)]);
    assert_reject_violated(&p, &new, Some(&old), None, "Monotonic decreased");
}

// ===========================================================================
// 8. StrictMonotonic
// ===========================================================================

#[test]
fn strict_monotonic_accepts_strictly_increasing() {
    let p = single_predicate(StateConstraint::StrictMonotonic { index: 1 });
    let old = state_with(&[(1, 5)]);
    let new = state_with(&[(1, 6)]);
    assert_accept(&p, &new, Some(&old), None, "StrictMonotonic positive");
}

#[test]
fn strict_monotonic_rejects_equal() {
    let p = single_predicate(StateConstraint::StrictMonotonic { index: 1 });
    let old = state_with(&[(1, 5)]);
    let new = state_with(&[(1, 5)]);
    assert_reject_violated(&p, &new, Some(&old), None, "StrictMonotonic equal");
}

#[test]
fn strict_monotonic_rejects_decreasing() {
    let p = single_predicate(StateConstraint::StrictMonotonic { index: 1 });
    let old = state_with(&[(1, 5)]);
    let new = state_with(&[(1, 4)]);
    assert_reject_violated(&p, &new, Some(&old), None, "StrictMonotonic decrease");
}

// ===========================================================================
// 9. BoundedBy
// ===========================================================================

#[test]
fn bounded_by_accepts_change_when_witness_set() {
    let p = single_predicate(StateConstraint::BoundedBy {
        index: 0,
        witness_index: 1,
    });
    let old = state_with(&[]);
    let new = state_with(&[(0, 10), (1, 1)]);
    assert_accept(&p, &new, Some(&old), None, "BoundedBy armed");
}

#[test]
fn bounded_by_rejects_change_when_witness_zero() {
    let p = single_predicate(StateConstraint::BoundedBy {
        index: 0,
        witness_index: 1,
    });
    let old = state_with(&[]);
    let new = state_with(&[(0, 10)]); // witness slot still zero
    assert_reject_violated(&p, &new, Some(&old), None, "BoundedBy unarmed");
}

#[test]
fn bounded_by_accepts_no_change_regardless_of_witness() {
    let p = single_predicate(StateConstraint::BoundedBy {
        index: 0,
        witness_index: 1,
    });
    let old = state_with(&[(0, 10)]);
    let new = state_with(&[(0, 10)]);
    assert_accept(&p, &new, Some(&old), None, "BoundedBy no change");
}

// ===========================================================================
// 10. FieldDelta
// ===========================================================================

#[test]
fn field_delta_accepts_exact_increment() {
    let p = single_predicate(StateConstraint::FieldDelta {
        index: 0,
        delta: field_from_u64(5),
    });
    let old = state_with(&[(0, 10)]);
    let new = state_with(&[(0, 15)]);
    assert_accept(&p, &new, Some(&old), None, "FieldDelta positive");
}

#[test]
fn field_delta_rejects_wrong_increment() {
    let p = single_predicate(StateConstraint::FieldDelta {
        index: 0,
        delta: field_from_u64(5),
    });
    let old = state_with(&[(0, 10)]);
    let new = state_with(&[(0, 16)]);
    assert_reject_violated(&p, &new, Some(&old), None, "FieldDelta wrong");
}

// ===========================================================================
// 11. FieldDeltaInRange
// ===========================================================================

#[test]
fn field_delta_in_range_accepts_inside_bounds() {
    let p = single_predicate(StateConstraint::FieldDeltaInRange {
        index: 0,
        min_delta: field_from_u64(1),
        max_delta: field_from_u64(10),
    });
    let old = state_with(&[(0, 100)]);
    assert_accept(
        &p,
        &state_with(&[(0, 101)]),
        Some(&old),
        None,
        "FieldDeltaInRange lower",
    );
    assert_accept(
        &p,
        &state_with(&[(0, 110)]),
        Some(&old),
        None,
        "FieldDeltaInRange upper",
    );
    assert_accept(
        &p,
        &state_with(&[(0, 105)]),
        Some(&old),
        None,
        "FieldDeltaInRange middle",
    );
}

#[test]
fn field_delta_in_range_rejects_below_min() {
    let p = single_predicate(StateConstraint::FieldDeltaInRange {
        index: 0,
        min_delta: field_from_u64(2),
        max_delta: field_from_u64(10),
    });
    let old = state_with(&[(0, 100)]);
    let new = state_with(&[(0, 101)]);
    assert_reject_violated(&p, &new, Some(&old), None, "FieldDeltaInRange below");
}

#[test]
fn field_delta_in_range_rejects_above_max() {
    let p = single_predicate(StateConstraint::FieldDeltaInRange {
        index: 0,
        min_delta: field_from_u64(1),
        max_delta: field_from_u64(5),
    });
    let old = state_with(&[(0, 100)]);
    let new = state_with(&[(0, 106)]);
    assert_reject_violated(&p, &new, Some(&old), None, "FieldDeltaInRange above");
}

// ===========================================================================
// 12. FieldGteHeight
// ===========================================================================

fn ctx_at(height: u64) -> EvalContext {
    EvalContext::minimal(height, 0)
}

#[test]
fn field_gte_height_accepts_at_bound() {
    let p = single_predicate(StateConstraint::FieldGteHeight {
        index: 0,
        offset: 100,
    });
    let new = state_with(&[(0, 200)]);
    let ctx = ctx_at(100);
    assert_accept(&p, &new, None, Some(&ctx), "FieldGteHeight at bound");
}

#[test]
fn field_gte_height_rejects_below_bound() {
    let p = single_predicate(StateConstraint::FieldGteHeight {
        index: 0,
        offset: 100,
    });
    let new = state_with(&[(0, 199)]);
    let ctx = ctx_at(100);
    assert_reject_violated(&p, &new, None, Some(&ctx), "FieldGteHeight below");
}

#[test]
fn field_gte_height_requires_context() {
    let p = single_predicate(StateConstraint::FieldGteHeight {
        index: 0,
        offset: 0,
    });
    let new = state_with(&[(0, 100)]);
    assert_reject_err(
        &p,
        &new,
        None,
        None,
        |e| {
            matches!(
                e,
                ProgramError::MissingContextField {
                    field: "block_height"
                }
            )
        },
        "FieldGteHeight no ctx",
    );
}

// ===========================================================================
// 13. FieldLteHeight
// ===========================================================================

#[test]
fn field_lte_height_accepts_at_bound() {
    let p = single_predicate(StateConstraint::FieldLteHeight {
        index: 0,
        offset: 100,
    });
    let new = state_with(&[(0, 200)]);
    let ctx = ctx_at(100);
    assert_accept(&p, &new, None, Some(&ctx), "FieldLteHeight at bound");
}

#[test]
fn field_lte_height_rejects_above_bound() {
    let p = single_predicate(StateConstraint::FieldLteHeight {
        index: 0,
        offset: 100,
    });
    let new = state_with(&[(0, 201)]);
    let ctx = ctx_at(100);
    assert_reject_violated(&p, &new, None, Some(&ctx), "FieldLteHeight above");
}

// ===========================================================================
// 14. SumEqualsAcross
// ===========================================================================

#[test]
fn sum_equals_across_accepts_balanced_transition() {
    // Invariant: sum(new[in]) == sum(old[in]) + sum(new[out]).
    //   old_in = 4, new_in = 10, new_out = 6 → 10 == 4 + 6.
    let p = single_predicate(StateConstraint::SumEqualsAcross {
        input_fields: vec![0],
        output_fields: vec![1],
    });
    let old = state_with(&[(0, 4), (1, 0)]);
    let new = state_with(&[(0, 10), (1, 6)]);
    assert_accept(&p, &new, Some(&old), None, "SumEqualsAcross balanced");
}

#[test]
fn sum_equals_across_rejects_unbalanced() {
    let p = single_predicate(StateConstraint::SumEqualsAcross {
        input_fields: vec![0],
        output_fields: vec![1],
    });
    let old = state_with(&[(0, 4), (1, 0)]);
    let new = state_with(&[(0, 10), (1, 5)]); // delta input = 6, output = 5 → mismatch
    assert_reject_violated(&p, &new, Some(&old), None, "SumEqualsAcross unbalanced");
}

// ===========================================================================
// 15. SenderAuthorized
// ===========================================================================

#[test]
fn sender_authorized_requires_context_sender() {
    let p = single_predicate(StateConstraint::SenderAuthorized {
        set: AuthorizedSet::PublicRoot { set_root_index: 7 },
    });
    let mut state = CellState::default();
    state.fields[7] = field_from_u64(42);
    // ctx with no sender — should reject
    let ctx = EvalContext::minimal(0, 0);
    assert_reject_err(
        &p,
        &state,
        None,
        Some(&ctx),
        |e| matches!(e, ProgramError::MissingContextField { field: "sender" }),
        "SenderAuthorized missing sender",
    );
}

#[test]
fn sender_authorized_blinded_set_with_valid_witness_accepts() {
    let commitment = [0xABu8; 32];
    let p = single_predicate(StateConstraint::SenderAuthorized {
        set: AuthorizedSet::BlindedSet { commitment },
    });
    let registry = WitnessedPredicateRegistry::with_stubs();
    let proof = b"stub-blinded-set-proof";
    let blobs: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
        kind: WitnessKindTag::ProofBytes,
        bytes: proof,
    }];
    let witnesses = WitnessBundle {
        blobs: &blobs,
        registry: Some(&registry),
    };
    let ctx = EvalContext {
        sender: Some([0x05u8; 32]),
        ..Default::default()
    };

    let result = p.evaluate_full(
        &CellState::default(),
        None,
        Some(&ctx),
        &TransitionMeta::wildcard(),
        &witnesses,
    );
    assert!(
        result.is_ok(),
        "SenderAuthorized BlindedSet should dispatch through explicit stub registry, got: {result:?}"
    );
}

#[test]
fn sender_authorized_blinded_set_with_tampered_witness_rejects() {
    let commitment = [0xABu8; 32];
    let p = single_predicate(StateConstraint::SenderAuthorized {
        set: AuthorizedSet::BlindedSet { commitment },
    });
    let registry = WitnessedPredicateRegistry::with_stubs();
    let blobs: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
        kind: WitnessKindTag::ProofBytes,
        bytes: b"",
    }];
    let witnesses = WitnessBundle {
        blobs: &blobs,
        registry: Some(&registry),
    };
    let ctx = EvalContext {
        sender: Some([0x05u8; 32]),
        ..Default::default()
    };

    let err = p
        .evaluate_full(
            &CellState::default(),
            None,
            Some(&ctx),
            &TransitionMeta::wildcard(),
            &witnesses,
        )
        .expect_err("empty BlindedSet proof must reject");
    assert!(
        matches!(
            err,
            ProgramError::WitnessedPredicateRejected {
                kind_name: "BlindedSet",
                ..
            }
        ),
        "expected WitnessedPredicateRejected(BlindedSet), got: {err:?}"
    );
}

// ===========================================================================
// 16. CapabilityUniqueness
// ===========================================================================

#[test]
fn capability_uniqueness_structural_accept() {
    // Per CAVEAT-LAYER-COVERAGE.md §1 row 16: today cell-side evaluator is
    // structural only — it checks slot index validity and returns Ok. So a
    // declared CapabilityUniqueness on a valid slot accepts any transition.
    let p = single_predicate(StateConstraint::CapabilityUniqueness {
        cap_set_root_slot: 6,
    });
    let new = state_with(&[(6, 0xdeadbeef)]);
    assert_accept(&p, &new, None, None, "CapabilityUniqueness structural");
}

#[test]
fn capability_uniqueness_rejects_invalid_index() {
    let p = single_predicate(StateConstraint::CapabilityUniqueness {
        cap_set_root_slot: 99,
    });
    let new = CellState::default();
    assert_reject_err(
        &p,
        &new,
        None,
        None,
        |e| matches!(e, ProgramError::InvalidFieldIndex { .. }),
        "CapabilityUniqueness invalid index",
    );
}

#[test]
#[ignore = "blocked on cap-set Merkle uniqueness gadget — out of caveat-correctness lane scope (CAVEAT-LAYER-COVERAGE.md §1 row 16, §9)"]
fn capability_uniqueness_rejects_multiple_live_caps() {
    panic!("blocked");
}

// ===========================================================================
// 17. RateLimit
// ===========================================================================

#[test]
fn rate_limit_accepts_below_threshold_when_ctx_supplied() {
    // Cell-side evaluator reads ctx.sender_epoch_count; if caller supplies a
    // value below the cap, the variant accepts. (The executor today supplies
    // 0 always — that bug is tested in `state_constraint_executor.rs`.)
    let p = single_predicate(StateConstraint::RateLimit {
        max_per_epoch: 5,
        epoch_duration: 1024,
    });
    let new = CellState::default();
    let mut ctx = EvalContext::minimal(0, 0);
    ctx.sender = Some([1u8; 32]);
    ctx.sender_epoch_count = 3;
    assert_accept(&p, &new, None, Some(&ctx), "RateLimit below threshold");
}

#[test]
fn rate_limit_rejects_at_or_above_threshold_when_ctx_supplied() {
    let p = single_predicate(StateConstraint::RateLimit {
        max_per_epoch: 5,
        epoch_duration: 1024,
    });
    let new = CellState::default();
    let mut ctx = EvalContext::minimal(0, 0);
    ctx.sender = Some([1u8; 32]);
    ctx.sender_epoch_count = 5;
    assert_reject_violated(&p, &new, None, Some(&ctx), "RateLimit at threshold");
}

#[test]
fn rate_limit_accepts_count_witness_when_ctx_count_unset() {
    let p = single_predicate(StateConstraint::RateLimit {
        max_per_epoch: 5,
        epoch_duration: 1024,
    });
    let count = 4u32.to_le_bytes();
    let blobs: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
        kind: WitnessKindTag::RateLimitCount,
        bytes: &count,
    }];
    let witnesses = WitnessBundle {
        blobs: &blobs,
        registry: None,
    };
    let ctx = EvalContext {
        sender: Some([1u8; 32]),
        sender_epoch_count: 0,
        ..Default::default()
    };

    let result = p.evaluate_full(
        &CellState::default(),
        None,
        Some(&ctx),
        &TransitionMeta::wildcard(),
        &witnesses,
    );
    assert!(
        result.is_ok(),
        "RateLimit should accept under-cap RateLimitCount witness, got: {result:?}"
    );
}

#[test]
fn rate_limit_rejects_count_witness_at_cap_when_ctx_count_unset() {
    let p = single_predicate(StateConstraint::RateLimit {
        max_per_epoch: 5,
        epoch_duration: 1024,
    });
    let count = 5u32.to_le_bytes();
    let blobs: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
        kind: WitnessKindTag::RateLimitCount,
        bytes: &count,
    }];
    let witnesses = WitnessBundle {
        blobs: &blobs,
        registry: None,
    };
    let ctx = EvalContext {
        sender: Some([1u8; 32]),
        sender_epoch_count: 0,
        ..Default::default()
    };

    let err = p
        .evaluate_full(
            &CellState::default(),
            None,
            Some(&ctx),
            &TransitionMeta::wildcard(),
            &witnesses,
        )
        .expect_err("at-cap RateLimitCount witness must reject");
    assert!(
        matches!(err, ProgramError::ConstraintViolated { .. }),
        "expected ConstraintViolated, got: {err:?}"
    );
}

#[test]
#[ignore = "blocked on caveat-correctness: executor wires per-(cell,sender,epoch) counter into EvalContext.sender_epoch_count (CAVEAT-LAYER-COVERAGE.md §6.2, top-5 #3)"]
fn rate_limit_executor_honors_counter() {
    panic!("blocked");
}

// ===========================================================================
// 18. RateLimitBySum
// ===========================================================================

#[test]
fn rate_limit_by_sum_accepts_small_increment() {
    // Per CAVEAT-LAYER-COVERAGE.md §1 row 18: today evaluates as a per-turn
    // delta-bound on the last-8-bytes lane.
    let p = single_predicate(StateConstraint::RateLimitBySum {
        slot_index: 0,
        max_sum_per_epoch: 100,
        epoch_duration: 1024,
    });
    let old = state_with(&[(0, 10)]);
    let new = state_with(&[(0, 60)]); // delta = 50 ≤ 100
    assert_accept(&p, &new, Some(&old), None, "RateLimitBySum small delta");
}

#[test]
fn rate_limit_by_sum_rejects_increment_above_cap() {
    let p = single_predicate(StateConstraint::RateLimitBySum {
        slot_index: 0,
        max_sum_per_epoch: 100,
        epoch_duration: 1024,
    });
    let old = state_with(&[(0, 10)]);
    let new = state_with(&[(0, 200)]); // delta = 190 > 100
    assert_reject_violated(&p, &new, Some(&old), None, "RateLimitBySum exceeds cap");
}

#[test]
#[ignore = "blocked on caveat-correctness: per-(cell, slot, window) running-sum tracker into ctx (CAVEAT-LAYER-COVERAGE.md §1 row 18)"]
fn rate_limit_by_sum_running_window_enforcement() {
    panic!("blocked");
}

// ===========================================================================
// 19. TemporalGate
// ===========================================================================

#[test]
fn temporal_gate_accepts_inside_window() {
    let p = single_predicate(StateConstraint::TemporalGate {
        not_before: Some(100),
        not_after: Some(200),
    });
    let new = CellState::default();
    let ctx = ctx_at(150);
    assert_accept(&p, &new, None, Some(&ctx), "TemporalGate inside");
}

#[test]
fn temporal_gate_rejects_before_window() {
    let p = single_predicate(StateConstraint::TemporalGate {
        not_before: Some(100),
        not_after: Some(200),
    });
    let new = CellState::default();
    let ctx = ctx_at(99);
    assert_reject_violated(&p, &new, None, Some(&ctx), "TemporalGate before");
}

#[test]
fn temporal_gate_rejects_after_window() {
    let p = single_predicate(StateConstraint::TemporalGate {
        not_before: Some(100),
        not_after: Some(200),
    });
    let new = CellState::default();
    let ctx = ctx_at(201);
    assert_reject_violated(&p, &new, None, Some(&ctx), "TemporalGate after");
}

#[test]
fn temporal_gate_open_ended_lower() {
    let p = single_predicate(StateConstraint::TemporalGate {
        not_before: None,
        not_after: Some(50),
    });
    let new = CellState::default();
    assert_accept(&p, &new, None, Some(&ctx_at(0)), "TemporalGate open lower");
    assert_reject_violated(&p, &new, None, Some(&ctx_at(51)), "TemporalGate after");
}

// ===========================================================================
// 20. PreimageGate
// ===========================================================================

#[test]
fn preimage_gate_missing_preimage_in_ctx_rejects() {
    // Per CAVEAT-LAYER-COVERAGE.md §1 row 20: executor supplies
    // revealed_preimage: None unconditionally. The cell-side evaluator
    // returns MissingContextField. Until witness_blobs plumbing lands, this
    // is the documented behavior.
    let preimage = b"hello world!";
    let commitment = *blake3::hash(preimage).as_bytes();
    let mut new = CellState::default();
    new.fields[0] = commitment;
    let p = single_predicate(StateConstraint::PreimageGate {
        commitment_index: 0,
        hash_kind: HashKind::Blake3,
    });
    let ctx = EvalContext::minimal(0, 0);
    assert_reject_err(
        &p,
        &new,
        None,
        Some(&ctx),
        |e| matches!(e, ProgramError::PreimageWitnessMissing),
        "PreimageGate missing preimage",
    );
}

#[test]
fn preimage_gate_accepts_when_preimage_matches() {
    // When a caller (not the executor today) supplies the preimage in ctx,
    // the cell-side evaluator hashes it and compares — should accept the
    // matching preimage.
    let preimage = [7u8; 32];
    let commitment = *blake3::hash(&preimage).as_bytes();
    let mut new = CellState::default();
    new.fields[0] = commitment;
    let p = single_predicate(StateConstraint::PreimageGate {
        commitment_index: 0,
        hash_kind: HashKind::Blake3,
    });
    let mut ctx = EvalContext::minimal(0, 0);
    ctx.revealed_preimage = Some(preimage);
    assert_accept(&p, &new, None, Some(&ctx), "PreimageGate match");
}

#[test]
fn preimage_gate_rejects_wrong_preimage() {
    let preimage_real = [7u8; 32];
    let preimage_fake = [8u8; 32];
    let commitment = *blake3::hash(&preimage_real).as_bytes();
    let mut new = CellState::default();
    new.fields[0] = commitment;
    let p = single_predicate(StateConstraint::PreimageGate {
        commitment_index: 0,
        hash_kind: HashKind::Blake3,
    });
    let mut ctx = EvalContext::minimal(0, 0);
    ctx.revealed_preimage = Some(preimage_fake);
    assert_reject_violated(&p, &new, None, Some(&ctx), "PreimageGate wrong preimage");
}

#[test]
#[ignore = "blocked on caveat-correctness: Poseidon2 PreimageGate uses a BLAKE3-tagged stub today (CAVEAT-LAYER-COVERAGE.md §1 row 20)"]
fn preimage_gate_poseidon2_real_gadget() {
    panic!("blocked");
}

// ===========================================================================
// 21. MonotonicSequence
// ===========================================================================

#[test]
fn monotonic_sequence_accepts_plus_one() {
    let p = single_predicate(StateConstraint::MonotonicSequence { seq_index: 0 });
    let old = state_with(&[(0, 5)]);
    let new = state_with(&[(0, 6)]);
    assert_accept(&p, &new, Some(&old), None, "MonotonicSequence +1");
}

#[test]
fn monotonic_sequence_rejects_plus_two() {
    let p = single_predicate(StateConstraint::MonotonicSequence { seq_index: 0 });
    let old = state_with(&[(0, 5)]);
    let new = state_with(&[(0, 7)]);
    assert_reject_violated(&p, &new, Some(&old), None, "MonotonicSequence skip");
}

#[test]
fn monotonic_sequence_rejects_no_change() {
    let p = single_predicate(StateConstraint::MonotonicSequence { seq_index: 0 });
    let old = state_with(&[(0, 5)]);
    let new = state_with(&[(0, 5)]);
    assert_reject_violated(&p, &new, Some(&old), None, "MonotonicSequence no change");
}

// ===========================================================================
// 22. AllowedTransitions
// ===========================================================================

#[test]
fn allowed_transitions_accepts_listed_pair() {
    let p = single_predicate(StateConstraint::AllowedTransitions {
        slot_index: 0,
        allowed: vec![
            (field_from_u64(1), field_from_u64(2)),
            (field_from_u64(2), field_from_u64(3)),
        ],
    });
    let old = state_with(&[(0, 1)]);
    let new = state_with(&[(0, 2)]);
    assert_accept(&p, &new, Some(&old), None, "AllowedTransitions listed");
}

#[test]
fn allowed_transitions_rejects_unlisted_pair() {
    let p = single_predicate(StateConstraint::AllowedTransitions {
        slot_index: 0,
        allowed: vec![(field_from_u64(1), field_from_u64(2))],
    });
    let old = state_with(&[(0, 1)]);
    let new = state_with(&[(0, 5)]);
    assert_reject_violated(&p, &new, Some(&old), None, "AllowedTransitions unlisted");
}

// ===========================================================================
// 23. TemporalPredicate (sentinel-rejected today)
// ===========================================================================

#[test]
fn temporal_predicate_returns_sentinel_today() {
    let p = single_predicate(StateConstraint::TemporalPredicate {
        witness_index: 0,
        dsl_hash: [9u8; 32],
    });
    let new = CellState::default();
    assert_reject_err(
        &p,
        &new,
        None,
        None,
        |e| matches!(e, ProgramError::TemporalPredicateWitnessMissing { .. }),
        "TemporalPredicate sentinel",
    );
}

#[test]
#[ignore = "blocked on caveat-correctness lane: registry dispatch of TemporalPredicate via circuit::temporal_predicate_dsl (CAVEAT-LAYER-COVERAGE.md §6.1, #1)"]
fn temporal_predicate_accepts_with_valid_witness() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on caveat-correctness lane: TemporalPredicate witness tampering rejection"]
fn temporal_predicate_rejects_with_tampered_witness() {
    panic!("blocked");
}

// ===========================================================================
// 24. BoundDelta (sentinel-rejected today)
// ===========================================================================

#[test]
fn bound_delta_returns_sentinel_today() {
    use dregg_cell::CellId;
    let p = single_predicate(StateConstraint::BoundDelta {
        local_slot: 0,
        peer_cell: CellId([1u8; 32]),
        peer_slot: 0,
        delta_relation: DeltaRelation::EqualAndOpposite,
    });
    let new = CellState::default();
    assert_reject_err(
        &p,
        &new,
        None,
        None,
        |e| matches!(e, ProgramError::BoundDeltaNotWired { .. }),
        "BoundDelta sentinel",
    );
}

#[test]
#[ignore = "blocked on caveat-correctness multi-cell-eval portion: γ.2 cross-cell wiring (CAVEAT-LAYER-COVERAGE.md §1 row 24, §6.1)"]
fn bound_delta_accepts_matching_peer_delta() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on caveat-correctness multi-cell-eval portion: BoundDelta peer-mismatch rejection"]
fn bound_delta_rejects_mismatched_peer_delta() {
    panic!("blocked");
}

// ===========================================================================
// 25. AnyOf
// ===========================================================================

#[test]
fn any_of_accepts_when_at_least_one_holds() {
    let p = single_predicate(StateConstraint::AnyOf {
        variants: vec![
            SimpleStateConstraint::FieldEquals {
                index: 0,
                value: field_from_u64(1),
            },
            SimpleStateConstraint::FieldEquals {
                index: 0,
                value: field_from_u64(2),
            },
        ],
    });
    assert_accept(&p, &state_with(&[(0, 1)]), None, None, "AnyOf left holds");
    assert_accept(&p, &state_with(&[(0, 2)]), None, None, "AnyOf right holds");
}

#[test]
fn any_of_rejects_when_none_hold() {
    let p = single_predicate(StateConstraint::AnyOf {
        variants: vec![
            SimpleStateConstraint::FieldEquals {
                index: 0,
                value: field_from_u64(1),
            },
            SimpleStateConstraint::FieldEquals {
                index: 0,
                value: field_from_u64(2),
            },
        ],
    });
    assert_reject_violated(&p, &state_with(&[(0, 3)]), None, None, "AnyOf none hold");
}

#[test]
fn any_of_with_empty_variants_rejects() {
    let p = single_predicate(StateConstraint::AnyOf { variants: vec![] });
    let new = CellState::default();
    // Empty disjunction is unsatisfiable.
    let res = p.evaluate(&new, None, None);
    assert!(res.is_err(), "AnyOf empty must reject");
}

// ===========================================================================
// 26. Witnessed (sentinel-rejected today)
// ===========================================================================

#[test]
fn witnessed_returns_sentinel_today() {
    let p = single_predicate(StateConstraint::Witnessed {
        wp: WitnessedPredicate::dfa([1u8; 32], InputRef::Sender, 0),
    });
    let new = CellState::default();
    assert_reject_err(
        &p,
        &new,
        None,
        None,
        |e| matches!(e, ProgramError::WitnessedPredicateRequiresExecutor { .. }),
        "Witnessed sentinel",
    );
}

#[test]
fn witnessed_dfa_with_valid_proof_accepts() {
    let p = single_predicate(StateConstraint::Witnessed {
        wp: WitnessedPredicate::dfa([1u8; 32], InputRef::Sender, 0),
    });
    let registry = WitnessedPredicateRegistry::with_stubs();
    let proof = b"stub-dfa-proof";
    let blobs: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
        kind: WitnessKindTag::ProofBytes,
        bytes: proof,
    }];
    let witnesses = WitnessBundle {
        blobs: &blobs,
        registry: Some(&registry),
    };
    let new = CellState::default();
    let ctx = EvalContext {
        sender: Some([0xA5u8; 32]),
        ..Default::default()
    };

    let result = p.evaluate_full(
        &new,
        None,
        Some(&ctx),
        &TransitionMeta::wildcard(),
        &witnesses,
    );
    assert!(
        result.is_ok(),
        "Dfa plumbing should accept non-empty proof via explicit stub registry, got: {result:?}"
    );
}

#[test]
fn witnessed_dfa_with_tampered_proof_rejects() {
    let commitment = [1u8; 32];
    let sender = [0xA5u8; 32];
    let p = single_predicate(StateConstraint::Witnessed {
        wp: WitnessedPredicate::dfa(commitment, InputRef::Sender, 0),
    });
    let registry = exact_dfa_registry(commitment, sender, b"valid-dfa-proof");
    let proof = b"tampered-dfa-proof";
    let blobs: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
        kind: WitnessKindTag::ProofBytes,
        bytes: proof,
    }];
    let witnesses = WitnessBundle {
        blobs: &blobs,
        registry: Some(&registry),
    };
    let new = CellState::default();
    let ctx = EvalContext {
        sender: Some(sender),
        ..Default::default()
    };

    let err = p
        .evaluate_full(
            &new,
            None,
            Some(&ctx),
            &TransitionMeta::wildcard(),
            &witnesses,
        )
        .expect_err("Dfa verifier must reject mismatched proof bytes");
    assert!(
        matches!(
            &err,
            ProgramError::WitnessedPredicateRejected {
                kind_name: "Dfa",
                reason,
                ..
            } if reason.contains("exact-dfa-state-constraint-test-verifier")
                && reason.contains("proof mismatch")
        ),
        "expected WitnessedPredicateRejected(Dfa) from exact verifier, got: {err:?}"
    );
}

#[test]
fn witnessed_unknown_kind_rejects() {
    let p = single_predicate(StateConstraint::Witnessed {
        wp: WitnessedPredicate::custom([0xEEu8; 32], [0xC0u8; 32], InputRef::Sender, 0),
    });
    let registry = WitnessedPredicateRegistry::empty();
    let proof = b"custom-proof";
    let blobs: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
        kind: WitnessKindTag::ProofBytes,
        bytes: proof,
    }];
    let witnesses = WitnessBundle {
        blobs: &blobs,
        registry: Some(&registry),
    };
    let new = CellState::default();
    let ctx = EvalContext {
        sender: Some([0xA5u8; 32]),
        ..Default::default()
    };

    let err = p
        .evaluate_full(
            &new,
            None,
            Some(&ctx),
            &TransitionMeta::wildcard(),
            &witnesses,
        )
        .expect_err("unknown custom witnessed predicate kind must reject");
    assert!(
        matches!(
            err,
            ProgramError::WitnessedPredicateRejected {
                kind_name: "Custom",
                ..
            }
        ),
        "expected WitnessedPredicateRejected(Custom), got: {err:?}"
    );
}

// ===========================================================================
// 27. Custom (sentinel-rejected today)
// ===========================================================================

#[test]
fn custom_returns_sentinel_today() {
    let p = single_predicate(StateConstraint::Custom {
        ir_hash: [3u8; 32],
        descriptor: CustomDescriptor::default(),
        reads: ReadSet::default(),
    });
    let new = CellState::default();
    assert_reject_err(
        &p,
        &new,
        None,
        None,
        |e| matches!(e, ProgramError::CustomConstraintUnevaluable { .. }),
        "Custom sentinel",
    );
}

#[test]
#[ignore = "blocked on DSL-IR runtime dispatch — separate workstream (CAVEAT-LAYER-COVERAGE.md §1 row 27)"]
fn custom_accepts_when_dsl_runtime_resolves() {
    panic!("blocked");
}

// ===========================================================================
// 28. Renounced (sentinel-rejected today — requires executor-side registry)
// ===========================================================================

#[test]
fn renounced_returns_sentinel_without_registry() {
    // Per CAVEAT-LAYER-COVERAGE.md §1 row 28 (Renounced):
    // `StateConstraint::Renounced` dispatches through the
    // `WitnessedPredicateKind::NonMembership` verifier in the executor
    // registry. Without a registry the cell-side evaluator returns
    // `SenderMembershipWitnessMissing` — the same sentinel as
    // `SenderAuthorized` in the no-registry path. This is fail-closed:
    // a cell declaring `Renounced` is unreachable today (bricked) until
    // the caveat-correctness lane wires the NonMembership verifier.
    use dregg_cell::program::RenouncedSet;
    let p = single_predicate(StateConstraint::Renounced {
        set: RenouncedSet::BlindedSet {
            commitment: [0xABu8; 32],
        },
    });
    let new = CellState::default();
    // No ctx needed — the sentinel fires before ctx lookup.
    assert_reject_err(
        &p,
        &new,
        None,
        None,
        |e| matches!(e, ProgramError::MissingContextField { field: "sender" }),
        "Renounced without ctx returns sentinel",
    );
}

#[test]
fn renounced_public_root_returns_sentinel_without_registry() {
    // Same sentinel shape for the `PublicRoot` sub-variant of `RenouncedSet`.
    use dregg_cell::program::RenouncedSet;
    let p = single_predicate(StateConstraint::Renounced {
        set: RenouncedSet::PublicRoot { set_root_index: 0 },
    });
    let new = CellState::default();
    assert_reject_err(
        &p,
        &new,
        None,
        None,
        |e| matches!(e, ProgramError::MissingContextField { field: "sender" }),
        "Renounced PublicRoot without ctx returns sentinel",
    );
}

#[test]
fn renounced_accepts_when_sender_not_in_set() {
    // Sender 0x05.. is strictly between lower=0x04.. and upper=0x06..;
    // the SortedNeighborNonMembershipVerifier (registered in default_builtins)
    // must accept the proof and the program must evaluate Ok(()).
    use dregg_cell::predicate::{NonMembershipNeighborProof, WitnessedPredicateRegistry};
    use dregg_cell::program::{
        RenouncedSet, TransitionMeta, WitnessBlobView, WitnessBundle, WitnessKindTag,
    };

    let commitment = [0xABu8; 32];
    let candidate = [0x05u8; 32];
    let proof = NonMembershipNeighborProof::new(&commitment, [0x04u8; 32], [0x06u8; 32]);
    let proof_bytes = proof.to_bytes();

    let registry = WitnessedPredicateRegistry::default_builtins();
    let blobs: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
        kind: WitnessKindTag::ProofBytes,
        bytes: &proof_bytes,
    }];
    let bundle = WitnessBundle {
        blobs: &blobs,
        registry: Some(&registry),
    };
    let p = single_predicate(StateConstraint::Renounced {
        set: RenouncedSet::BlindedSet { commitment },
    });
    let new = CellState::default();
    let ctx = EvalContext {
        sender: Some(candidate),
        ..Default::default()
    };
    let result = p.evaluate_full(&new, None, Some(&ctx), &TransitionMeta::wildcard(), &bundle);
    assert!(
        result.is_ok(),
        "valid non-membership proof must be accepted, got: {result:?}"
    );
}

#[test]
fn renounced_rejects_when_sender_in_set() {
    // Adversarial: sender == lower neighbor — the prover IS in the set.
    // The neighbor invariant `lower < candidate` is violated; verifier rejects.
    use dregg_cell::predicate::{NonMembershipNeighborProof, WitnessedPredicateRegistry};
    use dregg_cell::program::{
        RenouncedSet, TransitionMeta, WitnessBlobView, WitnessBundle, WitnessKindTag,
    };

    let commitment = [0xABu8; 32];
    let candidate = [0x05u8; 32];
    // lower == candidate: the prover IS on the lower boundary (i.e., in the set).
    let proof = NonMembershipNeighborProof::new(&commitment, candidate, [0x06u8; 32]);
    let proof_bytes = proof.to_bytes();

    let registry = WitnessedPredicateRegistry::default_builtins();
    let blobs: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
        kind: WitnessKindTag::ProofBytes,
        bytes: &proof_bytes,
    }];
    let bundle = WitnessBundle {
        blobs: &blobs,
        registry: Some(&registry),
    };
    let p = single_predicate(StateConstraint::Renounced {
        set: RenouncedSet::BlindedSet { commitment },
    });
    let new = CellState::default();
    let ctx = EvalContext {
        sender: Some(candidate),
        ..Default::default()
    };
    let err = p
        .evaluate_full(&new, None, Some(&ctx), &TransitionMeta::wildcard(), &bundle)
        .expect_err("candidate-in-set must be rejected");
    assert!(
        matches!(
            err,
            ProgramError::WitnessedPredicateRejected {
                kind_name: "NonMembership",
                ..
            }
        ),
        "expected WitnessedPredicateRejected(NonMembership), got: {err:?}"
    );
}

// ===========================================================================
// 29. SenderAuthorized with CredentialSet sub-variant (sentinel today)
// ===========================================================================

#[test]
fn sender_authorized_credential_set_sentinel_without_registry() {
    // `AuthorizedSet::CredentialSet` dispatches to the `BlindedSet`
    // verifier against a commitment derived from `(issuer_cell,
    // schema_id)`. Without an executor-side registry the sentinel
    // `SenderMembershipWitnessMissing` fires (same path as BlindedSet).
    let p = single_predicate(StateConstraint::SenderAuthorized {
        set: AuthorizedSet::CredentialSet {
            issuer_cell: [0x01u8; 32],
            credential_schema_id: [0x02u8; 32],
        },
    });
    let new = CellState::default();
    let ctx = EvalContext::minimal(0, 0);
    assert_reject_err(
        &p,
        &new,
        None,
        Some(&ctx),
        |e| matches!(e, ProgramError::MissingContextField { field: "sender" }),
        "SenderAuthorized CredentialSet returns sentinel without ctx.sender",
    );
}

#[test]
#[ignore = "blocked on caveat-correctness: CredentialSet credential-gated voting path (starbridge-governed-namespace) — needs BlindedSet verifier + issuer cell out-of-band lookup"]
fn sender_authorized_credential_set_accepts_with_valid_presentation() {
    panic!("blocked");
}

// ===========================================================================
// Operation-scoped Cases (CellProgram::Cases — Cav-Codex Block 4)
// ===========================================================================

#[test]
fn cases_default_deny_when_no_case_matches() {
    // Empty case list ⇒ no match ⇒ default-deny.
    let p = CellProgram::Cases(vec![]);
    let new = CellState::default();
    let res = p.evaluate(&new, None, None);
    assert!(
        matches!(res, Err(ProgramError::NoTransitionCaseMatched)),
        "Cases empty must default-deny, got {res:?}"
    );
}

#[test]
fn cases_always_guard_with_no_constraints_accepts_everything() {
    let p = CellProgram::Cases(vec![TransitionCase {
        guard: TransitionGuard::Always,
        constraints: vec![],
    }]);
    let new = state_with(&[(0, 9999)]);
    assert_accept(&p, &new, None, None, "Cases Always wide open");
}

#[test]
fn cases_method_is_send_advances_head_only() {
    let p = CellProgram::Cases(vec![
        TransitionCase {
            guard: TransitionGuard::Always,
            constraints: vec![StateConstraint::Immutable { index: 1 }],
        },
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("send"),
            },
            constraints: vec![StateConstraint::MonotonicSequence { seq_index: 0 }],
        },
    ]);
    let old = state_with(&[(0, 4), (1, 99)]);
    let new = state_with(&[(0, 5), (1, 99)]);
    let meta = TransitionMeta::new(symbol("send"), EFFECT_SET_FIELD);
    let result = p.evaluate_with_meta(&new, Some(&old), None, &meta);
    assert!(
        result.is_ok(),
        "send case should accept head +1 while preserving invariant slot, got: {result:?}"
    );
}

#[test]
fn cases_wrong_method_rejected() {
    let p = CellProgram::Cases(vec![
        TransitionCase {
            guard: TransitionGuard::Always,
            constraints: vec![StateConstraint::Immutable { index: 1 }],
        },
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("send"),
            },
            constraints: vec![StateConstraint::MonotonicSequence { seq_index: 0 }],
        },
    ]);
    let old = state_with(&[(0, 4), (1, 99)]);
    let new = state_with(&[(0, 5), (1, 99)]);
    let meta = TransitionMeta::new(symbol("receive"), EFFECT_SET_FIELD);
    let result = p.evaluate_with_meta(&new, Some(&old), None, &meta);
    assert!(
        matches!(result, Err(ProgramError::NoTransitionCaseMatched)),
        "operation-binding Cases must reject unmatched methods, got: {result:?}"
    );
}
