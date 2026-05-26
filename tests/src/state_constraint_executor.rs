//! `StateConstraint` exercised through the full `TurnExecutor`.
//!
//! Layer: **executor integration**. Each test sets up a cell with a
//! `CellProgram::Predicate(...)` containing one constraint, then runs a
//! turn through `TurnExecutor::execute`. The point of THIS layer (vs.
//! `state_constraint_variants.rs`) is to catch the placeholder-context
//! regressions documented in CAVEAT-LAYER-COVERAGE.md §6.2 and §6.3 —
//! the executor builds `EvalContext` at `turn/src/executor.rs:4361-4373`
//! with `sender_epoch_count: 0` and `revealed_preimage: None` hard-coded.
//! Those defaults silently subvert `RateLimit` and `PreimageGate`.
//!
//! Tests are marked `#[ignore]` with the unblock-by-lane label when they
//! depend on the caveat-correctness lane wiring the missing context.

use std::{collections::HashMap, sync::Arc};

use dregg_cell::predicate::{
    PredicateInput, WitnessedPredicateError, WitnessedPredicateKind, WitnessedPredicateRegistry,
    WitnessedPredicateVerifier,
};
use dregg_cell::{
    field_from_u64, AuthRequired, Cell, CellId, CellProgram, Ledger, Permissions, StateConstraint,
};
use dregg_turn::action::{symbol, WitnessBlob};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, Turn, TurnExecutor,
    TurnResult,
};

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

fn make_cell_with_program(seed: u8, balance: u64, program: CellProgram) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(7);
    let token_id = [0u8; 32];
    let mut cell = Cell::with_balance(pk, token_id, balance);
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

fn build_set_field_turn(
    agent: CellId,
    nonce: u64,
    field_idx: u8,
    value: dregg_cell::FieldElement,
) -> Turn {
    build_set_field_turn_with_witnesses(agent, nonce, field_idx, value, vec![])
}

fn build_set_field_turn_with_witnesses(
    agent: CellId,
    nonce: u64,
    field_idx: u8,
    value: dregg_cell::FieldElement,
    witness_blobs: Vec<WitnessBlob>,
) -> Turn {
    let mut forest = CallForest::new();
    let action = Action {
        target: agent,
        method: symbol("set_field"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::SetField {
            cell: agent,
            index: field_idx as usize,
            value,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs,
    };
    forest.add_root(action);

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

fn build_transfer_turn(agent: CellId, peer: CellId, amount: u64, nonce: u64) -> Turn {
    let mut forest = CallForest::new();
    let action = Action {
        target: agent,
        method: symbol("transfer"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::Transfer {
            from: agent,
            to: peer,
            amount,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    };
    forest.add_root(action);

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

fn exact_sender_registry(
    kind: WitnessedPredicateKind,
    name: &'static str,
    expected_commitment: [u8; 32],
    expected_sender: [u8; 32],
    expected_proof: &'static [u8],
) -> WitnessedPredicateRegistry {
    let mut registry = WitnessedPredicateRegistry::empty();
    registry.register_builtin(Arc::new(ExactSenderVerifier {
        kind,
        name,
        expected_commitment,
        expected_sender,
        expected_proof,
    }));
    registry
}

// ===========================================================================
// Static + transition variants — executor accepts when constraint holds
// ===========================================================================

#[test]
fn executor_accepts_set_field_when_field_equals_holds() {
    let program = CellProgram::Predicate(vec![StateConstraint::FieldEquals {
        index: 0,
        value: field_from_u64(42),
    }]);
    let agent_cell = make_cell_with_program(1, 1000, program);
    let agent = agent_cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent_cell).unwrap();

    let turn = build_set_field_turn(agent, 0, 0, field_from_u64(42));
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        matches!(result, TurnResult::Committed { .. }),
        "expected accept, got: {result:?}"
    );
}

#[test]
fn executor_rejects_set_field_when_field_equals_violated() {
    let program = CellProgram::Predicate(vec![StateConstraint::FieldEquals {
        index: 0,
        value: field_from_u64(42),
    }]);
    let agent_cell = make_cell_with_program(2, 1000, program);
    let agent = agent_cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent_cell).unwrap();

    // Try to set a different value → must reject (ProgramViolation).
    let turn = build_set_field_turn(agent, 0, 0, field_from_u64(43));
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        matches!(result, TurnResult::Rejected { .. }),
        "expected reject, got: {result:?}"
    );
}

#[test]
fn executor_accepts_monotonic_increase() {
    let program = CellProgram::Predicate(vec![StateConstraint::Monotonic { index: 0 }]);
    let agent_cell = make_cell_with_program(3, 1000, program);
    let agent = agent_cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent_cell).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());

    // First turn: 0 → 5 (legal: 5 ≥ 0).
    let turn1 = build_set_field_turn(agent, 0, 0, field_from_u64(5));
    let r1 = executor.execute(&turn1, &mut ledger);
    let prev_receipt_hash = match r1 {
        TurnResult::Committed { receipt, .. } => receipt.receipt_hash(),
        other => panic!("turn1: {other:?}"),
    };

    // Second turn: 5 → 10 (legal).
    let mut turn2 = build_set_field_turn(agent, 1, 0, field_from_u64(10));
    turn2.previous_receipt_hash = Some(prev_receipt_hash);
    let r2 = executor.execute(&turn2, &mut ledger);
    assert!(matches!(r2, TurnResult::Committed { .. }), "turn2: {r2:?}");
}

#[test]
fn executor_rejects_monotonic_decrease() {
    let program = CellProgram::Predicate(vec![StateConstraint::Monotonic { index: 0 }]);
    let agent_cell = make_cell_with_program(4, 1000, program);
    let agent = agent_cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent_cell).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let t1 = build_set_field_turn(agent, 0, 0, field_from_u64(50));
    let _ = executor.execute(&t1, &mut ledger);

    let t2 = build_set_field_turn(agent, 1, 0, field_from_u64(40));
    let r2 = executor.execute(&t2, &mut ledger);
    assert!(
        matches!(r2, TurnResult::Rejected { .. }),
        "expected reject on decrease, got: {r2:?}"
    );
}

#[test]
fn executor_rejects_immutable_change() {
    let program = CellProgram::Predicate(vec![StateConstraint::Immutable { index: 1 }]);
    let agent_cell = make_cell_with_program(5, 1000, program);
    let agent = agent_cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent_cell).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    // First write OK (init).
    let t1 = build_set_field_turn(agent, 0, 1, field_from_u64(99));
    let _ = executor.execute(&t1, &mut ledger);

    // Second write must be rejected.
    let t2 = build_set_field_turn(agent, 1, 1, field_from_u64(100));
    let r2 = executor.execute(&t2, &mut ledger);
    assert!(matches!(r2, TurnResult::Rejected { .. }), "got: {r2:?}");
}

// ===========================================================================
// TemporalGate — uses ctx.block_height (executor wires this honestly)
// ===========================================================================

#[test]
fn executor_temporal_gate_inside_window_accepts() {
    let program = CellProgram::Predicate(vec![StateConstraint::TemporalGate {
        not_before: Some(0),
        not_after: Some(u64::MAX),
    }]);
    let agent_cell = make_cell_with_program(6, 1000, program);
    let agent = agent_cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent_cell).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let turn = build_set_field_turn(agent, 0, 0, field_from_u64(1));
    let r = executor.execute(&turn, &mut ledger);
    assert!(matches!(r, TurnResult::Committed { .. }), "got: {r:?}");
}

#[test]
fn executor_rate_limit_count_witness_under_cap_accepts() {
    let program = CellProgram::Predicate(vec![StateConstraint::RateLimit {
        max_per_epoch: 3,
        epoch_duration: 1024,
    }]);
    let agent_cell = make_cell_with_program(17, 1000, program);
    let agent = agent_cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent_cell).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let turn = build_set_field_turn_with_witnesses(
        agent,
        0,
        0,
        field_from_u64(1),
        vec![WitnessBlob::rate_limit_count(2)],
    );
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        matches!(result, TurnResult::Committed { .. }),
        "expected executor to thread under-cap RateLimitCount witness, got: {result:?}"
    );
}

#[test]
fn executor_rate_limit_count_witness_at_cap_rejects() {
    let program = CellProgram::Predicate(vec![StateConstraint::RateLimit {
        max_per_epoch: 3,
        epoch_duration: 1024,
    }]);
    let agent_cell = make_cell_with_program(18, 1000, program);
    let agent = agent_cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent_cell).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let turn = build_set_field_turn_with_witnesses(
        agent,
        0,
        0,
        field_from_u64(1),
        vec![WitnessBlob::rate_limit_count(3)],
    );
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        matches!(result, TurnResult::Rejected { .. }),
        "expected executor to reject at-cap RateLimitCount witness, got: {result:?}"
    );
}

#[test]
fn executor_rate_limit_by_sum_delta_under_cap_accepts() {
    let program = CellProgram::Predicate(vec![StateConstraint::RateLimitBySum {
        slot_index: 0,
        max_sum_per_epoch: 100,
        epoch_duration: 1024,
    }]);
    let agent_cell = make_cell_with_program(21, 1000, program);
    let agent = agent_cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent_cell).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let turn = build_set_field_turn(agent, 0, 0, field_from_u64(60));
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        matches!(result, TurnResult::Committed { .. }),
        "expected executor to accept per-turn sum delta under cap, got: {result:?}"
    );
}

#[test]
fn executor_rate_limit_by_sum_delta_over_cap_rejects() {
    let program = CellProgram::Predicate(vec![StateConstraint::RateLimitBySum {
        slot_index: 0,
        max_sum_per_epoch: 100,
        epoch_duration: 1024,
    }]);
    let agent_cell = make_cell_with_program(22, 1000, program);
    let agent = agent_cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent_cell).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let turn = build_set_field_turn(agent, 0, 0, field_from_u64(101));
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        matches!(result, TurnResult::Rejected { .. }),
        "expected executor to reject per-turn sum delta over cap, got: {result:?}"
    );
}

// ===========================================================================
// Placeholder-context regressions (CAVEAT-LAYER-COVERAGE.md §6.2)
// ===========================================================================

#[test]
fn executor_rate_limit_actually_limits() {
    let program = CellProgram::Predicate(vec![StateConstraint::RateLimit {
        max_per_epoch: 2,
        epoch_duration: 1024,
    }]);
    let agent_cell = make_cell_with_program(23, 1000, program);
    let agent = agent_cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent_cell).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());

    let first = build_set_field_turn(agent, 0, 0, field_from_u64(1));
    let first_result = executor.execute(&first, &mut ledger);
    let first_hash = match &first_result {
        TurnResult::Committed { receipt, .. } => receipt.receipt_hash(),
        other => panic!("first under-cap turn should commit, got: {other:?}"),
    };

    let mut second = build_set_field_turn(agent, 1, 0, field_from_u64(2));
    second.previous_receipt_hash = Some(first_hash);
    let second_result = executor.execute(&second, &mut ledger);
    let second_hash = match &second_result {
        TurnResult::Committed { receipt, .. } => receipt.receipt_hash(),
        other => panic!("second under-cap turn should commit, got: {other:?}"),
    };

    let mut third = build_set_field_turn(agent, 2, 0, field_from_u64(3));
    third.previous_receipt_hash = Some(second_hash);
    let third_result = executor.execute(&third, &mut ledger);
    assert!(
        matches!(third_result, TurnResult::Rejected { .. }),
        "third same-epoch mutation must be rejected at the cap, got: {third_result:?}"
    );
}

#[test]
fn executor_preimage_gate_with_valid_witness_accepts() {
    let preimage = [0x42u8; 32];
    let commitment = *blake3::hash(&preimage).as_bytes();
    let program = CellProgram::Predicate(vec![StateConstraint::PreimageGate {
        commitment_index: 0,
        hash_kind: dregg_cell::program::HashKind::Blake3,
    }]);
    let agent_cell = make_cell_with_program(15, 1000, program);
    let agent = agent_cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent_cell).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let turn = build_set_field_turn_with_witnesses(
        agent,
        0,
        0,
        commitment,
        vec![WitnessBlob::preimage(preimage)],
    );
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        matches!(result, TurnResult::Committed { .. }),
        "expected executor to accept valid PreimageGate witness, got: {result:?}"
    );
}

#[test]
fn executor_preimage_gate_with_wrong_witness_rejects() {
    let preimage = [0x42u8; 32];
    let wrong_preimage = [0x24u8; 32];
    let commitment = *blake3::hash(&preimage).as_bytes();
    let program = CellProgram::Predicate(vec![StateConstraint::PreimageGate {
        commitment_index: 0,
        hash_kind: dregg_cell::program::HashKind::Blake3,
    }]);
    let agent_cell = make_cell_with_program(16, 1000, program);
    let agent = agent_cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent_cell).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let turn = build_set_field_turn_with_witnesses(
        agent,
        0,
        0,
        commitment,
        vec![WitnessBlob::preimage(wrong_preimage)],
    );
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        matches!(result, TurnResult::Rejected { .. }),
        "expected executor to reject tampered PreimageGate witness, got: {result:?}"
    );
}

// ===========================================================================
// Sentinel-rejected variants surface as TurnError::ProgramViolation
// ===========================================================================

#[test]
fn executor_rejects_cell_declaring_temporal_predicate_variant_today() {
    // Per CAVEAT-LAYER-COVERAGE.md §6.1 / top-5 #1: any cell that declares
    // TemporalPredicate is bricked today — the cell-side evaluator returns
    // a sentinel, the executor surfaces it as ProgramViolation.
    let program = CellProgram::Predicate(vec![StateConstraint::TemporalPredicate {
        witness_index: 0,
        dsl_hash: [9u8; 32],
    }]);
    let agent_cell = make_cell_with_program(7, 1000, program);
    let agent = agent_cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent_cell).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let turn = build_set_field_turn(agent, 0, 0, field_from_u64(1));
    let r = executor.execute(&turn, &mut ledger);
    assert!(
        matches!(r, TurnResult::Rejected { .. }),
        "expected reject (sentinel pass-through), got: {r:?}"
    );
}

#[test]
fn executor_rejects_cell_declaring_witnessed_variant_today() {
    use dregg_cell::predicate::WitnessedPredicate;
    use dregg_cell::InputRef;
    let program = CellProgram::Predicate(vec![StateConstraint::Witnessed {
        wp: WitnessedPredicate::dfa([1u8; 32], InputRef::Sender, 0),
    }]);
    let agent_cell = make_cell_with_program(8, 1000, program);
    let agent = agent_cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent_cell).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let turn = build_set_field_turn(agent, 0, 0, field_from_u64(1));
    let r = executor.execute(&turn, &mut ledger);
    assert!(matches!(r, TurnResult::Rejected { .. }), "got: {r:?}");
}

#[test]
fn executor_witnessed_dfa_with_stub_registry_accepts() {
    use dregg_cell::predicate::WitnessedPredicate;
    use dregg_cell::InputRef;
    use dregg_cell::WitnessedPredicateRegistry;

    let program = CellProgram::Predicate(vec![StateConstraint::Witnessed {
        wp: WitnessedPredicate::dfa([1u8; 32], InputRef::Sender, 0),
    }]);
    let agent_cell = make_cell_with_program(19, 1000, program);
    let agent = agent_cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent_cell).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero())
        .with_witnessed_registry(WitnessedPredicateRegistry::with_stubs());
    let turn = build_set_field_turn_with_witnesses(
        agent,
        0,
        0,
        field_from_u64(1),
        vec![WitnessBlob::proof(b"stub-dfa-proof".to_vec())],
    );
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        matches!(result, TurnResult::Committed { .. }),
        "expected executor to route Witnessed DFA through explicit stub registry, got: {result:?}"
    );
}

#[test]
fn executor_rejects_cell_declaring_custom_variant_today() {
    use dregg_cell::program::{CustomDescriptor, ReadSet};
    let program = CellProgram::Predicate(vec![StateConstraint::Custom {
        ir_hash: [3u8; 32],
        descriptor: CustomDescriptor::default(),
        reads: ReadSet::default(),
    }]);
    let agent_cell = make_cell_with_program(9, 1000, program);
    let agent = agent_cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent_cell).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let turn = build_set_field_turn(agent, 0, 0, field_from_u64(1));
    let r = executor.execute(&turn, &mut ledger);
    assert!(matches!(r, TurnResult::Rejected { .. }), "got: {r:?}");
}

#[test]
fn executor_rejects_cell_declaring_bound_delta_variant_today() {
    use dregg_cell::program::DeltaRelation;
    let program = CellProgram::Predicate(vec![StateConstraint::BoundDelta {
        local_slot: 0,
        peer_cell: CellId([42u8; 32]),
        peer_slot: 0,
        delta_relation: DeltaRelation::EqualAndOpposite,
    }]);
    let agent_cell = make_cell_with_program(10, 1000, program);
    let agent = agent_cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent_cell).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let turn = build_set_field_turn(agent, 0, 0, field_from_u64(1));
    let r = executor.execute(&turn, &mut ledger);
    assert!(matches!(r, TurnResult::Rejected { .. }), "got: {r:?}");
}

// ===========================================================================
// SenderAuthorized — needs sender + membership witness registry
// ===========================================================================

#[test]
fn executor_sender_authorized_with_membership_witness_accepts() {
    use dregg_cell::program::AuthorizedSet;

    let set_root = [0x31u8; 32];
    let program = CellProgram::Predicate(vec![StateConstraint::SenderAuthorized {
        set: AuthorizedSet::PublicRoot { set_root_index: 0 },
    }]);
    let agent_cell = make_cell_with_program(20, 1000, program);
    let agent = agent_cell.id();
    let expected_sender = *agent_cell.public_key();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent_cell).unwrap();

    let executor =
        TurnExecutor::new(ComputronCosts::zero()).with_witnessed_registry(exact_sender_registry(
            WitnessedPredicateKind::MerkleMembership,
            "exact-merkle-membership-executor-test-verifier",
            set_root,
            expected_sender,
            b"valid-membership-proof",
        ));
    let turn = build_set_field_turn_with_witnesses(
        agent,
        0,
        0,
        set_root,
        vec![WitnessBlob::merkle_path(b"valid-membership-proof".to_vec())],
    );
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        matches!(result, TurnResult::Committed { .. }),
        "expected executor to route SenderAuthorized Merkle witness through explicit stub registry, got: {result:?}"
    );
}

#[test]
fn executor_sender_authorized_rejects_non_member() {
    use dregg_cell::program::AuthorizedSet;

    let set_root = [0x32u8; 32];
    let program = CellProgram::Predicate(vec![StateConstraint::SenderAuthorized {
        set: AuthorizedSet::PublicRoot { set_root_index: 0 },
    }]);
    let agent_cell = make_cell_with_program(23, 1000, program);
    let agent = agent_cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent_cell).unwrap();

    let executor =
        TurnExecutor::new(ComputronCosts::zero()).with_witnessed_registry(exact_sender_registry(
            WitnessedPredicateKind::MerkleMembership,
            "exact-merkle-membership-executor-test-verifier",
            set_root,
            [0xEEu8; 32],
            b"valid-membership-proof",
        ));
    let turn = build_set_field_turn_with_witnesses(
        agent,
        0,
        0,
        set_root,
        vec![WitnessBlob::merkle_path(b"valid-membership-proof".to_vec())],
    );
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        matches!(result, TurnResult::Rejected { .. }),
        "expected executor to reject SenderAuthorized when registry rejects sender, got: {result:?}"
    );
}

// ===========================================================================
// Renounced — executor rejects today (requires NonMembership verifier)
// ===========================================================================

#[test]
fn executor_rejects_cell_declaring_renounced_variant_today() {
    // Per CAVEAT-LAYER-COVERAGE.md §1 row 28: `StateConstraint::Renounced`
    // requires the executor to wire a `WitnessedPredicateKind::NonMembership`
    // verifier into the `WitnessBundle`. Today the executor does not supply a
    // registry, so the cell-side evaluator returns `MissingContextField
    // { field: "sender" }` (fail-closed sentinel). The executor surfaces it
    // as `TurnResult::Rejected`.
    use dregg_cell::program::RenouncedSet;
    let program = CellProgram::Predicate(vec![StateConstraint::Renounced {
        set: RenouncedSet::BlindedSet {
            commitment: [0xCDu8; 32],
        },
    }]);
    let agent_cell = make_cell_with_program(11, 1000, program);
    let agent = agent_cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent_cell).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let turn = build_set_field_turn(agent, 0, 0, field_from_u64(1));
    let r = executor.execute(&turn, &mut ledger);
    assert!(
        matches!(r, TurnResult::Rejected { .. }),
        "expected reject (Renounced sentinel), got: {r:?}"
    );
}

#[test]
fn executor_renounced_accepts_when_sender_not_in_set() {
    // Cell declares Renounced { BlindedSet { commitment } }.
    // Agent (sender) has pk with first byte 0x0B; proof brackets it between
    // lower=0x0A.. and upper=0x0C..  The executor wires default_builtins()
    // (SortedNeighborNonMembershipVerifier), and the action carries the 96-byte
    // neighbor proof as a ProofBytes witness blob.
    use dregg_cell::predicate::NonMembershipNeighborProof;
    use dregg_cell::program::RenouncedSet;
    use dregg_turn::action::{WitnessBlob, WitnessKind};

    let commitment = [0xABu8; 32];
    // Agent pk is controlled by make_cell_with_program(seed=11, …):
    //   pk[0] = 11 = 0x0B, pk[31] = 11*7 = 77 = 0x4D, rest = 0x00.
    // lower = [0x0A; 32]: 0x0A00…00 < 0x0B00…00 ✓
    // upper = [0x0C; 32]: 0x0B00…00 < 0x0C00…00 ✓
    let mut lower = [0u8; 32];
    lower[0] = 0x0A;
    let mut upper = [0u8; 32];
    upper[0] = 0x0C;

    let proof = NonMembershipNeighborProof::new(&commitment, lower, upper);
    let proof_bytes = proof.to_bytes().to_vec();

    let program = CellProgram::Predicate(vec![StateConstraint::Renounced {
        set: RenouncedSet::BlindedSet { commitment },
    }]);
    let agent_cell = make_cell_with_program(11, 1000, program);
    let agent = agent_cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent_cell).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());

    // Build a SetField turn carrying the non-membership proof as a ProofBytes blob.
    let mut forest = CallForest::new();
    let action = Action {
        target: agent,
        method: symbol("set_field"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::SetField {
            cell: agent,
            index: 0,
            value: field_from_u64(1),
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![WitnessBlob::new(WitnessKind::ProofBytes, proof_bytes)],
    };
    forest.add_root(action);

    let turn = Turn {
        agent,
        nonce: 0,
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
    };

    let r = executor.execute(&turn, &mut ledger);
    assert!(
        matches!(r, TurnResult::Committed { .. }),
        "valid non-membership proof must cause executor to accept, got: {r:?}"
    );
}

// ===========================================================================
// Transfer with BoundDelta on both sides → γ.2 territory
// ===========================================================================

#[test]
fn executor_bilateral_transfer_with_bound_delta_accepts() {
    use dregg_cell::program::DeltaRelation;

    let mut a = make_cell_with_program(24, 1000, CellProgram::None);
    let mut b = make_cell_with_program(25, 1000, CellProgram::None);
    let a_id = a.id();
    let b_id = b.id();
    a.state.fields[0] = field_from_u64(100);
    b.state.fields[0] = field_from_u64(20);
    a.capabilities.grant(b_id, AuthRequired::None).unwrap();
    a.program = CellProgram::Predicate(vec![StateConstraint::BoundDelta {
        local_slot: 0,
        peer_cell: b_id,
        peer_slot: 0,
        delta_relation: DeltaRelation::EqualAndOpposite,
    }]);
    b.program = CellProgram::Predicate(vec![StateConstraint::BoundDelta {
        local_slot: 0,
        peer_cell: a_id,
        peer_slot: 0,
        delta_relation: DeltaRelation::EqualAndOpposite,
    }]);

    let mut ledger = Ledger::new();
    ledger.insert_cell(a).unwrap();
    ledger.insert_cell(b).unwrap();

    let mut forest = CallForest::new();
    let action = Action {
        target: a_id,
        method: symbol("transfer"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![
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
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    };
    forest.add_root(action);
    let turn = Turn {
        agent: a_id,
        nonce: 0,
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
    };

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        matches!(result, TurnResult::Committed { .. }),
        "matching bilateral BoundDelta field transfer must commit, got: {result:?}"
    );
}
