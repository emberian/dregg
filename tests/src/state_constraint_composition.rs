//! Composition tests: multiple `StateConstraint` variants on one cell,
//! conjunction enforcement, and cross-cutting compositions with cap
//! caveats / `Authorization::Custom` / γ.2 binding.
//!
//! Each test in this file **explicitly notes** what variants / threats /
//! primitives it composes — composition tests are where the substrate
//! actually proves itself. Per the mandate: "atomicity" tests cover one
//! variant; "composition" tests cover the interactions that emerge when
//! multiple caveats fire on the same turn.
//!
//! Layer: cell-side evaluator + (where applicable) executor. Tests that
//! require pieces of the caveat-correctness lane to land carry an
//! `#[ignore = "..."]` with unblock label.

use dregg_cell::predicate::WitnessedPredicate;
use dregg_cell::program::SimpleStateConstraint;
use dregg_cell::{
    CellProgram, CellState, EvalContext, InputRef, ProgramError, StateConstraint, field_from_u64,
};

fn state_with(field_values: &[(usize, u64)]) -> CellState {
    let mut s = CellState::default();
    for (idx, val) in field_values {
        s.fields[*idx] = field_from_u64(*val);
    }
    s
}

// ===========================================================================
// Composition: Predicate(Vec<>) is a conjunction
// ===========================================================================

#[test]
fn predicate_vec_conjunction_all_must_hold() {
    // Composes: FieldEquals (slot 0 = 1) ∧ FieldGte (slot 1 ≥ 100) ∧ Immutable (slot 2).
    let constraints = vec![
        StateConstraint::FieldEquals {
            index: 0,
            value: field_from_u64(1),
        },
        StateConstraint::FieldGte {
            index: 1,
            value: field_from_u64(100),
        },
        StateConstraint::Immutable { index: 2 },
    ];
    let p = CellProgram::Predicate(constraints);

    let old = state_with(&[(2, 7)]);

    // Positive: all hold.
    let new = state_with(&[(0, 1), (1, 200), (2, 7)]);
    assert!(
        p.evaluate(&new, Some(&old), None).is_ok(),
        "all conjuncts hold"
    );

    // Negative: FieldEquals fails.
    let new = state_with(&[(0, 2), (1, 200), (2, 7)]);
    assert!(
        matches!(
            p.evaluate(&new, Some(&old), None),
            Err(ProgramError::ConstraintViolated { .. })
        ),
        "first conjunct must fail"
    );

    // Negative: Immutable fails.
    let new = state_with(&[(0, 1), (1, 200), (2, 8)]);
    assert!(
        matches!(
            p.evaluate(&new, Some(&old), None),
            Err(ProgramError::ConstraintViolated { .. })
        ),
        "last conjunct must fail"
    );
}

#[test]
fn predicate_vec_short_circuits_on_first_violation() {
    // Composes: FieldEquals (fails) + a sentinel-returning variant (TemporalPredicate).
    // If the conjunction short-circuits the first failure should win;
    // otherwise the sentinel may dominate. We allow either order — the
    // important thing is that the program rejects.
    let constraints = vec![
        StateConstraint::FieldEquals {
            index: 0,
            value: field_from_u64(1),
        },
        StateConstraint::TemporalPredicate {
            witness_index: 0,
            dsl_hash: [0u8; 32],
        },
    ];
    let p = CellProgram::Predicate(constraints);
    let new = state_with(&[(0, 9)]);
    assert!(p.evaluate(&new, None, None).is_err());
}

// ===========================================================================
// AnyOf composed with conjunction
// ===========================================================================

#[test]
fn any_of_inside_predicate_vec_works_as_or_inside_and() {
    // Composes: FieldEquals(0=1) ∧ (FieldEquals(1=2) ∨ FieldEquals(1=3)).
    let p = CellProgram::Predicate(vec![
        StateConstraint::FieldEquals {
            index: 0,
            value: field_from_u64(1),
        },
        StateConstraint::AnyOf {
            variants: vec![
                SimpleStateConstraint::FieldEquals {
                    index: 1,
                    value: field_from_u64(2),
                },
                SimpleStateConstraint::FieldEquals {
                    index: 1,
                    value: field_from_u64(3),
                },
            ],
        },
    ]);
    // Holds: slot0=1, slot1=2.
    assert!(
        p.evaluate(&state_with(&[(0, 1), (1, 2)]), None, None)
            .is_ok()
    );
    // Holds: slot0=1, slot1=3.
    assert!(
        p.evaluate(&state_with(&[(0, 1), (1, 3)]), None, None)
            .is_ok()
    );
    // Fails outer: slot0=2.
    assert!(
        p.evaluate(&state_with(&[(0, 2), (1, 2)]), None, None)
            .is_err()
    );
    // Fails AnyOf branch: slot0=1, slot1=4.
    assert!(
        p.evaluate(&state_with(&[(0, 1), (1, 4)]), None, None)
            .is_err()
    );
}

// ===========================================================================
// Mixed static + contextual + transition
// ===========================================================================

#[test]
fn mix_static_contextual_and_transition_constraints() {
    // Composes:
    //   FieldEquals(0=1)                    [static]
    //   TemporalGate(not_before=10)         [contextual]
    //   Monotonic(slot 1)                   [transition]
    let p = CellProgram::Predicate(vec![
        StateConstraint::FieldEquals {
            index: 0,
            value: field_from_u64(1),
        },
        StateConstraint::TemporalGate {
            not_before: Some(10),
            not_after: None,
        },
        StateConstraint::Monotonic { index: 1 },
    ]);
    let old = state_with(&[(1, 5)]);
    let new = state_with(&[(0, 1), (1, 7)]);
    let ctx = EvalContext::minimal(15, 0);
    assert!(p.evaluate(&new, Some(&old), Some(&ctx)).is_ok());

    // Block height below not_before → reject (TemporalGate fires).
    let ctx_early = EvalContext::minimal(5, 0);
    assert!(p.evaluate(&new, Some(&old), Some(&ctx_early)).is_err());

    // Slot 1 decreases → Monotonic fires.
    let new_bad = state_with(&[(0, 1), (1, 4)]);
    assert!(p.evaluate(&new_bad, Some(&old), Some(&ctx)).is_err());
}

// ===========================================================================
// Rate / window-sum composition
// ===========================================================================

#[test]
fn rate_limit_composes_with_temporal_gate_and_monotonic() {
    // Composes:
    //   TemporalGate(height in [10, 20])   [contextual]
    //   RateLimit(max 2 per epoch)         [contextual rate cap]
    //   Monotonic(slot 0)                  [transition]
    let p = CellProgram::Predicate(vec![
        StateConstraint::TemporalGate {
            not_before: Some(10),
            not_after: Some(20),
        },
        StateConstraint::RateLimit {
            max_per_epoch: 2,
            epoch_duration: 16,
        },
        StateConstraint::Monotonic { index: 0 },
    ]);
    let old = state_with(&[(0, 10)]);
    let new = state_with(&[(0, 11)]);

    let mut ctx = EvalContext::minimal(15, 0);
    ctx.sender = Some([7u8; 32]);
    ctx.sender_epoch_count = 1;
    assert!(
        p.evaluate(&new, Some(&old), Some(&ctx)).is_ok(),
        "inside window, under rate cap, and monotonic"
    );

    let mut at_cap = ctx.clone();
    at_cap.sender_epoch_count = 2;
    assert!(
        p.evaluate(&new, Some(&old), Some(&at_cap)).is_err(),
        "rate cap must reject even when temporal and monotonic constraints hold"
    );

    let decreasing = state_with(&[(0, 9)]);
    assert!(
        p.evaluate(&decreasing, Some(&old), Some(&ctx)).is_err(),
        "monotonic must reject even when temporal and rate constraints hold"
    );
}

#[test]
fn rate_limit_by_sum_composes_with_conservation() {
    // Composes:
    //   RateLimitBySum(slot 0 delta <= 25)         [window-sum approximation]
    //   SumEqualsAcross(input 0, output 1)         [intra-cell conservation]
    let p = CellProgram::Predicate(vec![
        StateConstraint::RateLimitBySum {
            slot_index: 0,
            max_sum_per_epoch: 25,
            epoch_duration: 64,
        },
        StateConstraint::SumEqualsAcross {
            input_fields: vec![0],
            output_fields: vec![1],
        },
    ]);
    let old = state_with(&[(0, 100), (1, 0)]);

    let balanced_under_cap = state_with(&[(0, 120), (1, 20)]);
    assert!(
        p.evaluate(&balanced_under_cap, Some(&old), None).is_ok(),
        "slot-0 delta is under cap and conservation holds"
    );

    let balanced_over_cap = state_with(&[(0, 140), (1, 40)]);
    assert!(
        p.evaluate(&balanced_over_cap, Some(&old), None).is_err(),
        "window-sum cap must reject even when conservation holds"
    );

    let unbalanced_under_cap = state_with(&[(0, 120), (1, 19)]);
    assert!(
        p.evaluate(&unbalanced_under_cap, Some(&old), None).is_err(),
        "conservation must reject even when the window-sum cap holds"
    );
}

// ===========================================================================
// Conservation + AllowedTransitions state-machine
// ===========================================================================

#[test]
fn conservation_with_state_machine_step() {
    // Composes: SumEqualsAcross (intra-cell conservation) + AllowedTransitions
    // (state field 7: open=1 → claimed=2 → delivered=3).
    let p = CellProgram::Predicate(vec![
        StateConstraint::SumEqualsAcross {
            input_fields: vec![0],
            output_fields: vec![1],
        },
        StateConstraint::AllowedTransitions {
            slot_index: 7,
            allowed: vec![
                (field_from_u64(1), field_from_u64(2)),
                (field_from_u64(2), field_from_u64(3)),
            ],
        },
    ]);
    let old = state_with(&[(0, 4), (1, 0), (7, 1)]);
    let new = state_with(&[(0, 10), (1, 6), (7, 2)]);
    assert!(
        p.evaluate(&new, Some(&old), None).is_ok(),
        "balanced + allowed transition"
    );

    // Conservation violated.
    let new_bad = state_with(&[(0, 10), (1, 5), (7, 2)]);
    assert!(
        p.evaluate(&new_bad, Some(&old), None).is_err(),
        "conservation breaks"
    );

    // State machine violated (skip to delivered without claiming).
    let new_bad2 = state_with(&[(0, 10), (1, 6), (7, 3)]);
    assert!(
        p.evaluate(&new_bad2, Some(&old), None).is_err(),
        "state machine skip"
    );
}

// ===========================================================================
// Cross-cutting: caveat-snapshot + fresh-witness predicate
// ===========================================================================

#[test]
#[ignore = "blocked on caveat-correctness lane: WitnessedPredicate snapshot replay (PREDICATE-INVENTORY §6.3) + registry dispatch"]
fn caveat_snapshot_plus_fresh_witness_composition() {
    // Composition target: a WitnessedPredicate kind whose evaluator reads
    // BOTH a slot snapshot from the cell program's last-receipt commitment
    // AND a fresh witness blob from the action — exercising the two-arm
    // dispatch path documented in PREDICATE-INVENTORY §6.3.
    panic!("blocked");
}

// ===========================================================================
// Cross-cutting: slot caveats + cap caveats + Auth::Custom
// ===========================================================================

#[test]
#[ignore = "blocked on AUTHORIZATION-CUSTOM-DESIGN lane + CapabilityCaveat enforcement (PREDICATE-INVENTORY §7.6 Phase 6)"]
fn slot_caveats_plus_cap_caveats_plus_auth_custom() {
    // Composition target (per the mandate's discipline):
    //   - Slot caveats: Monotonic(0) ∧ TemporalGate(...) on the target cell.
    //   - Cap caveats: CapabilityCaveat::Witnessed(...) on the cap the actor exercises.
    //   - Authorization::Custom { predicate } with InputRef::SigningMessage.
    // The turn passes only if ALL three layers accept.
    panic!("blocked");
}

#[test]
#[ignore = "blocked on AUTHORIZATION-CUSTOM-DESIGN lane: a tampered Auth::Custom predicate must reject even when slot caveats accept"]
fn tampered_auth_custom_rejected_even_when_slot_caveats_pass() {
    panic!("blocked");
}

// ===========================================================================
// Cross-cutting: γ.2 bilateral binding + slot caveats on both cells
// ===========================================================================

#[test]
#[ignore = "blocked on caveat-correctness multi-cell-eval + γ.2 Phase 1 (STAGE-7-GAMMA-2-PI-DESIGN.md)"]
fn bilateral_transfer_with_slot_caveats_on_both_sides() {
    // Both cells declare:
    //   - BoundDelta { peer_cell = other, EqualAndOpposite } on bal_lo.
    //   - Sender's cell: RateLimit (max 3/epoch).
    //   - Receiver's cell: Monotonic on bal_lo.
    // The γ.2 PI binding (transfer_id) joins the two per-cell proofs;
    // the slot caveats fire independently on each side. The turn must
    // be accepted iff:
    //   - Both BoundDeltas pair correctly (γ.2).
    //   - Sender's RateLimit is honored.
    //   - Receiver's bal_lo increase is monotonic.
    panic!("blocked");
}

// ===========================================================================
// Three-cell ring trade (Cav-Codex composition target)
// ===========================================================================

#[test]
#[ignore = "blocked on caveat-correctness multi-cell-eval: 3-cell BoundDelta ring"]
fn three_cell_ring_trade_bound_delta() {
    // A pays B, B pays C, C pays A — net delta on every cell = 0.
    // Each cell declares BoundDelta pointing at its successor in the ring.
    // The γ.2 match loop must verify the three pairings.
    panic!("blocked");
}

// ===========================================================================
// Cross-federation composition: CapTpDelivered + sovereign witness + bilateral
// ===========================================================================

#[test]
#[ignore = "blocked on caveat-correctness + γ.2 cross-federation + sovereign-witness AIR teeth (SOVEREIGN-WITNESS-AIR-DESIGN.md)"]
fn cross_federation_captp_delivered_with_sovereign_and_bilateral() {
    // Mandate composition target:
    //   - Federation A's turn signs a Transfer(A→B) using Authorization::Signature.
    //   - That turn's effect is mirrored on Federation B via Authorization::CapTpDelivered,
    //     referencing the introducer-signed handoff certificate.
    //   - B's mirroring turn is sovereign-witnessed (sovereign B cell has a witness).
    //   - Both cells have slot caveats (Monotonic, RateLimit).
    //   - γ.2 binds the bilateral transfer_id across the two federation's per-cell proofs.
    panic!("blocked");
}
