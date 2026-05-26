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

use std::{collections::HashMap, sync::Arc};

use dregg_cell::predicate::{
    PredicateInput, WitnessedPredicate, WitnessedPredicateError, WitnessedPredicateKind,
    WitnessedPredicateRegistry, WitnessedPredicateVerifier,
};
use dregg_cell::program::{
    SimpleStateConstraint, TransitionMeta, WitnessBlobView, WitnessBundle, WitnessKindTag,
};
use dregg_cell::{
    AuthRequired, Cell, CellId, CellProgram, CellState, EvalContext, InputRef, Ledger, Permissions,
    ProgramError, StateConstraint, field_from_u64,
};
use dregg_turn::action::{
    Action, Authorization, CommitmentMode, DelegationMode, WitnessBlob, symbol,
};
use dregg_turn::{CallForest, ComputronCosts, Effect, Turn, TurnBuilder, TurnExecutor, TurnResult};

fn state_with(field_values: &[(usize, u64)]) -> CellState {
    let mut s = CellState::default();
    for (idx, val) in field_values {
        s.fields[*idx] = field_from_u64(*val);
    }
    s
}

struct ExactSlotVerifier {
    vk_hash: [u8; 32],
    expected_commitment: [u8; 32],
    expected_slot: dregg_cell::FieldElement,
    expected_proof: &'static [u8],
}

impl WitnessedPredicateVerifier for ExactSlotVerifier {
    fn name(&self) -> &'static str {
        "composition-exact-slot-verifier"
    }

    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::Custom {
            vk_hash: self.vk_hash,
        }
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
            PredicateInput::Slot(slot) if **slot == self.expected_slot => {}
            PredicateInput::Slot(_) => {
                return Err(WitnessedPredicateError::Rejected {
                    kind_name: self.name(),
                    reason: "slot snapshot mismatch".into(),
                });
            }
            _ => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: self.name(),
                    expected: "Slot",
                    actual: "non-Slot",
                });
            }
        }
        if proof_bytes != self.expected_proof {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: self.name(),
                reason: "fresh witness proof mismatch".into(),
            });
        }
        Ok(())
    }
}

struct ExpectedCustomAuthVerifier {
    vk_hash: [u8; 32],
    expected_message: Vec<u8>,
    expected_proof: Vec<u8>,
}

impl WitnessedPredicateVerifier for ExpectedCustomAuthVerifier {
    fn name(&self) -> &'static str {
        "composition-expected-custom-auth-verifier"
    }

    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::Custom {
            vk_hash: self.vk_hash,
        }
    }

    fn verify(
        &self,
        _commitment: &[u8; 32],
        input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        match input {
            PredicateInput::SigningMessage(bytes) if *bytes == self.expected_message.as_slice() => {
            }
            PredicateInput::SigningMessage(_) => {
                return Err(WitnessedPredicateError::Rejected {
                    kind_name: self.name(),
                    reason: "signing message mismatch".into(),
                });
            }
            _ => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: self.name(),
                    expected: "SigningMessage",
                    actual: "non-SigningMessage",
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

fn make_custom_authorized_cell(seed: u8, vk_hash: [u8; 32], program: CellProgram) -> Cell {
    let mut public_key = [0u8; 32];
    public_key[0] = seed;
    let mut cell = Cell::with_balance(public_key, [0u8; 32], 1);
    cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::Custom { vk_hash },
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    cell.program = program;
    cell
}

fn make_open_programmed_cell(seed: u8, balance: u64, program: CellProgram) -> Cell {
    let mut public_key = [0u8; 32];
    public_key[0] = seed;
    public_key[31] = seed.wrapping_mul(7);
    let mut cell = Cell::with_balance(public_key, [0u8; 32], balance);
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
    cell.program = program;
    cell
}

fn set_fields_turn(agent: CellId, nonce: u64, effects: Vec<Effect>) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: agent,
        method: symbol("composition_set_fields"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects,
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    });
    Turn {
        agent,
        nonce,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

fn custom_set_field_action(
    target: CellId,
    predicate: WitnessedPredicate,
    proof: Vec<u8>,
) -> Action {
    Action {
        target,
        method: symbol("composition_custom_set_field"),
        args: vec![],
        authorization: Authorization::Custom { predicate },
        preconditions: Default::default(),
        effects: vec![Effect::SetField {
            cell: target,
            index: 0,
            value: field_from_u64(42),
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![WitnessBlob::proof(proof)],
    }
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
fn caveat_snapshot_plus_fresh_witness_composition() {
    // Composes:
    //   - FieldEquals on slot 0 (stable slot snapshot)
    //   - Monotonic on slot 1 (transition caveat)
    //   - Witnessed(Custom) that reads slot 0 and consumes fresh proof bytes.
    let vk_hash = [0xA1u8; 32];
    let commitment = [0xC1u8; 32];
    let proof = b"fresh-proof";
    let mut registry = WitnessedPredicateRegistry::empty();
    registry.register_custom(
        vk_hash,
        Arc::new(ExactSlotVerifier {
            vk_hash,
            expected_commitment: commitment,
            expected_slot: field_from_u64(7),
            expected_proof: proof,
        }),
    );
    let blobs = [WitnessBlobView {
        kind: WitnessKindTag::ProofBytes,
        bytes: proof,
    }];
    let witnesses = WitnessBundle {
        blobs: &blobs,
        registry: Some(&registry),
    };
    let program = CellProgram::Predicate(vec![
        StateConstraint::FieldEquals {
            index: 0,
            value: field_from_u64(7),
        },
        StateConstraint::Monotonic { index: 1 },
        StateConstraint::Witnessed {
            wp: WitnessedPredicate::custom(vk_hash, commitment, InputRef::Slot { index: 0 }, 0),
        },
    ]);
    let old = state_with(&[(1, 5)]);
    let new = state_with(&[(0, 7), (1, 6)]);
    program
        .evaluate_full(
            &new,
            Some(&old),
            None,
            &TransitionMeta::wildcard(),
            &witnesses,
        )
        .expect("slot caveats and fresh witnessed proof should compose");

    let stale_blobs = [WitnessBlobView {
        kind: WitnessKindTag::ProofBytes,
        bytes: b"stale-proof",
    }];
    let stale_witnesses = WitnessBundle {
        blobs: &stale_blobs,
        registry: Some(&registry),
    };
    assert!(
        program
            .evaluate_full(
                &new,
                Some(&old),
                None,
                &TransitionMeta::wildcard(),
                &stale_witnesses,
            )
            .is_err(),
        "stale proof bytes must reject even when slot caveats pass"
    );
}

// ===========================================================================
// Cross-cutting: slot caveats + Auth::Custom
// ===========================================================================

#[test]
fn slot_caveats_plus_auth_custom_accepts() {
    // Executor-level composition for the currently-live layers:
    //   - slot caveats: Monotonic(0) ∧ TemporalGate(...),
    //   - Authorization::Custom over InputRef::SigningMessage.
    //
    // CapabilityCaveat enforcement is a separate layer and remains covered by
    // its own blocked workstream; this test avoids pretending that cap caveats
    // are enforced here.
    let vk_hash = [0xB1u8; 32];
    let federation_id = [0xF1u8; 32];
    let proof = b"valid-proof".to_vec();
    let program = CellProgram::Predicate(vec![
        StateConstraint::TemporalGate {
            not_before: Some(0),
            not_after: None,
        },
        StateConstraint::Monotonic { index: 0 },
    ]);
    let cell = make_custom_authorized_cell(41, vk_hash, program);
    let target = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let predicate = WitnessedPredicate::custom(vk_hash, [0u8; 32], InputRef::SigningMessage, 0);
    let action = custom_set_field_action(target, predicate.clone(), proof.clone());
    let expected_message =
        TurnExecutor::compute_custom_signing_message(&action, &predicate, 0, &federation_id, 0);
    let mut registry = WitnessedPredicateRegistry::empty();
    registry.register_custom(
        vk_hash,
        Arc::new(ExpectedCustomAuthVerifier {
            vk_hash,
            expected_message,
            expected_proof: proof,
        }),
    );
    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_local_federation_id(federation_id);
    executor.set_witnessed_registry(registry);
    let mut builder = TurnBuilder::new(target, 0);
    builder.add_action(action);
    let result = executor.execute(&builder.fee(0).build(), &mut ledger);
    assert!(
        result.is_committed(),
        "slot-caveat-valid Authorization::Custom turn should commit, got {result:?}"
    );
    assert_eq!(
        ledger.get(&target).unwrap().state.fields[0],
        field_from_u64(42)
    );
}

#[test]
fn tampered_auth_custom_rejected_even_when_slot_caveats_pass() {
    // Executor-level composition:
    //   - target cell requires Authorization::Custom for set_state,
    //   - target cell program enforces slot caveats,
    //   - Custom verifier rejects the proof while the slot caveats would pass.
    let vk_hash = [0xB2u8; 32];
    let federation_id = [0xF2u8; 32];
    let program = CellProgram::Predicate(vec![
        StateConstraint::TemporalGate {
            not_before: Some(0),
            not_after: None,
        },
        StateConstraint::Monotonic { index: 0 },
    ]);
    let cell = make_custom_authorized_cell(42, vk_hash, program);
    let target = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let predicate = WitnessedPredicate::custom(vk_hash, [0u8; 32], InputRef::SigningMessage, 0);
    let action = custom_set_field_action(target, predicate.clone(), b"tampered-proof".to_vec());
    let expected_message =
        TurnExecutor::compute_custom_signing_message(&action, &predicate, 0, &federation_id, 0);
    let mut registry = WitnessedPredicateRegistry::empty();
    registry.register_custom(
        vk_hash,
        Arc::new(ExpectedCustomAuthVerifier {
            vk_hash,
            expected_message,
            expected_proof: b"valid-proof".to_vec(),
        }),
    );
    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_local_federation_id(federation_id);
    executor.set_witnessed_registry(registry);
    let mut builder = TurnBuilder::new(target, 0);
    builder.add_action(action);
    let result = executor.execute(&builder.fee(0).build(), &mut ledger);
    assert!(
        result.is_rejected(),
        "tampered Authorization::Custom proof must reject before committing slot-caveat-valid state"
    );
}

// ===========================================================================
// Cross-cutting: γ.2 bilateral binding + slot caveats on both cells
// ===========================================================================

#[test]
fn bilateral_transfer_with_slot_caveats_on_both_sides() {
    use dregg_cell::program::DeltaRelation;

    let mut sender = make_open_programmed_cell(0xA1, 1_000, CellProgram::None);
    let mut receiver = make_open_programmed_cell(0xB2, 1_000, CellProgram::None);
    let a_id = sender.id();
    let b_id = receiver.id();

    sender.program = CellProgram::Predicate(vec![
        StateConstraint::BoundDelta {
            local_slot: 0,
            peer_cell: b_id,
            peer_slot: 0,
            delta_relation: DeltaRelation::EqualAndOpposite,
        },
        StateConstraint::RateLimit {
            max_per_epoch: 3,
            epoch_duration: 16,
        },
    ]);
    receiver.program = CellProgram::Predicate(vec![
        StateConstraint::BoundDelta {
            local_slot: 0,
            peer_cell: a_id,
            peer_slot: 0,
            delta_relation: DeltaRelation::EqualAndOpposite,
        },
        StateConstraint::Monotonic { index: 0 },
    ]);

    sender.state.fields[0] = field_from_u64(100);
    receiver.state.fields[0] = field_from_u64(20);
    sender.capabilities.grant(b_id, AuthRequired::None).unwrap();

    let mut ledger = Ledger::new();
    ledger.insert_cell(sender).unwrap();
    ledger.insert_cell(receiver).unwrap();

    let turn = set_fields_turn(
        a_id,
        0,
        vec![
            Effect::SetField {
                cell: a_id,
                index: 0,
                value: field_from_u64(90),
            },
            Effect::SetField {
                cell: b_id,
                index: 0,
                value: field_from_u64(30),
            },
        ],
    );
    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
    assert!(
        matches!(result, TurnResult::Committed { .. }),
        "matching bilateral BoundDelta plus sender RateLimit and receiver Monotonic must commit, got: {result:?}"
    );

    let mut bad_sender = make_open_programmed_cell(0xA1, 1_000, CellProgram::None);
    let mut bad_receiver = make_open_programmed_cell(0xB2, 1_000, CellProgram::None);
    bad_sender.program = CellProgram::Predicate(vec![
        StateConstraint::BoundDelta {
            local_slot: 0,
            peer_cell: b_id,
            peer_slot: 0,
            delta_relation: DeltaRelation::EqualAndOpposite,
        },
        StateConstraint::RateLimit {
            max_per_epoch: 3,
            epoch_duration: 16,
        },
    ]);
    bad_receiver.program = CellProgram::Predicate(vec![
        StateConstraint::BoundDelta {
            local_slot: 0,
            peer_cell: a_id,
            peer_slot: 0,
            delta_relation: DeltaRelation::EqualAndOpposite,
        },
        StateConstraint::Monotonic { index: 0 },
    ]);
    bad_sender.state.fields[0] = field_from_u64(100);
    bad_receiver.state.fields[0] = field_from_u64(20);
    bad_sender
        .capabilities
        .grant(b_id, AuthRequired::None)
        .unwrap();

    let mut bad_ledger = Ledger::new();
    bad_ledger.insert_cell(bad_sender).unwrap();
    bad_ledger.insert_cell(bad_receiver).unwrap();
    let bad_turn = set_fields_turn(
        a_id,
        0,
        vec![
            Effect::SetField {
                cell: a_id,
                index: 0,
                value: field_from_u64(110),
            },
            Effect::SetField {
                cell: b_id,
                index: 0,
                value: field_from_u64(10),
            },
        ],
    );
    let bad_result = TurnExecutor::new(ComputronCosts::zero()).execute(&bad_turn, &mut bad_ledger);
    assert!(
        matches!(bad_result, TurnResult::Rejected { .. }),
        "BoundDelta-valid transfer must still reject when receiver Monotonic fails, got: {bad_result:?}"
    );
}

// ===========================================================================
// Three-cell ring trade (Cav-Codex composition target)
// ===========================================================================

#[test]
fn three_cell_ring_trade_bound_delta() {
    use dregg_cell::program::DeltaRelation;

    let program_for = |peer_cell| {
        CellProgram::Predicate(vec![StateConstraint::BoundDelta {
            local_slot: 0,
            peer_cell,
            peer_slot: 0,
            delta_relation: DeltaRelation::Equal,
        }])
    };

    let mut cell_a = make_open_programmed_cell(0xA1, 1_000, CellProgram::None);
    let mut cell_b = make_open_programmed_cell(0xB2, 1_000, CellProgram::None);
    let mut cell_c = make_open_programmed_cell(0xC3, 1_000, CellProgram::None);
    let a = cell_a.id();
    let b = cell_b.id();
    let c = cell_c.id();
    cell_a.program = program_for(b);
    cell_b.program = program_for(c);
    cell_c.program = program_for(a);
    cell_a.state.fields[0] = field_from_u64(10);
    cell_b.state.fields[0] = field_from_u64(20);
    cell_c.state.fields[0] = field_from_u64(30);
    cell_a.capabilities.grant(b, AuthRequired::None).unwrap();
    cell_a.capabilities.grant(c, AuthRequired::None).unwrap();

    let mut ledger = Ledger::new();
    ledger.insert_cell(cell_a).unwrap();
    ledger.insert_cell(cell_b).unwrap();
    ledger.insert_cell(cell_c).unwrap();
    let result = TurnExecutor::new(ComputronCosts::zero()).execute(
        &set_fields_turn(
            a,
            0,
            vec![
                Effect::SetField {
                    cell: a,
                    index: 0,
                    value: field_from_u64(15),
                },
                Effect::SetField {
                    cell: b,
                    index: 0,
                    value: field_from_u64(25),
                },
                Effect::SetField {
                    cell: c,
                    index: 0,
                    value: field_from_u64(35),
                },
            ],
        ),
        &mut ledger,
    );
    assert!(
        matches!(result, TurnResult::Committed { .. }),
        "three-cell BoundDelta ring with all peer deltas paired must commit, got: {result:?}"
    );

    let mut bad_a = make_open_programmed_cell(0xA1, 1_000, CellProgram::None);
    let mut bad_b = make_open_programmed_cell(0xB2, 1_000, CellProgram::None);
    let mut bad_c = make_open_programmed_cell(0xC3, 1_000, CellProgram::None);
    bad_a.program = program_for(b);
    bad_b.program = program_for(c);
    bad_c.program = program_for(a);
    bad_a.state.fields[0] = field_from_u64(10);
    bad_b.state.fields[0] = field_from_u64(20);
    bad_c.state.fields[0] = field_from_u64(30);
    bad_a.capabilities.grant(b, AuthRequired::None).unwrap();
    bad_a.capabilities.grant(c, AuthRequired::None).unwrap();
    let mut bad_ledger = Ledger::new();
    bad_ledger.insert_cell(bad_a).unwrap();
    bad_ledger.insert_cell(bad_b).unwrap();
    bad_ledger.insert_cell(bad_c).unwrap();
    let bad_result = TurnExecutor::new(ComputronCosts::zero()).execute(
        &set_fields_turn(
            a,
            0,
            vec![
                Effect::SetField {
                    cell: a,
                    index: 0,
                    value: field_from_u64(15),
                },
                Effect::SetField {
                    cell: b,
                    index: 0,
                    value: field_from_u64(25),
                },
                Effect::SetField {
                    cell: c,
                    index: 0,
                    value: field_from_u64(34),
                },
            ],
        ),
        &mut bad_ledger,
    );
    assert!(
        matches!(bad_result, TurnResult::Rejected { .. }),
        "three-cell BoundDelta ring with one unpaired delta must reject, got: {bad_result:?}"
    );
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
