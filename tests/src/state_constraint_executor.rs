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

use std::collections::HashMap;

use dregg_cell::{AuthRequired, Cell, CellId, CellProgram, Permissions};
use dregg_turn::action::symbol;
use dregg_turn::{Action, Authorization, CallForest, DelegationMode, Effect, Turn};

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
    assert!(matches!(r1, TurnResult::Committed { .. }), "turn1: {r1:?}");

    // Second turn: 5 → 10 (legal).
    let turn2 = build_set_field_turn(agent, 1, 0, field_from_u64(10));
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

// ===========================================================================
// Placeholder-context regressions (CAVEAT-LAYER-COVERAGE.md §6.2)
// ===========================================================================

#[test]
#[ignore = "blocked on caveat-correctness lane: executor must plumb sender_epoch_count into EvalContext (CAVEAT-LAYER-COVERAGE.md top-5 #3 / §6.2)"]
fn executor_rate_limit_actually_limits() {
    // Today: executor supplies sender_epoch_count: 0, so the cell-side check
    // ctx.sender_epoch_count >= max_per_epoch is always false and the
    // RateLimit always passes. This test runs `max_per_epoch + 1` turns
    // and asserts the (cap+1)th is rejected. It will fail until the
    // caveat-correctness lane lands the per-(cell,sender,epoch) counter
    // and wires it into the ctx build site.
    panic!("blocked");
}

#[test]
#[ignore = "blocked on caveat-correctness lane: executor must populate revealed_preimage from action.witness_blobs (CAVEAT-LAYER-COVERAGE.md top-5 #2)"]
fn executor_preimage_gate_with_valid_witness_accepts() {
    // Today: executor supplies revealed_preimage: None unconditionally;
    // PreimageGate always errors with MissingContextField. After the lane
    // lands witness_blobs lookup for WitnessKind::Preimage32, this test
    // submits a turn with the preimage witness blob and expects accept.
    panic!("blocked");
}

#[test]
#[ignore = "blocked on caveat-correctness lane: PreimageGate witness tampering rejection"]
fn executor_preimage_gate_with_wrong_witness_rejects() {
    panic!("blocked");
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
    use dregg_cell::InputRef;
    use dregg_cell::predicate::WitnessedPredicate;
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
// SenderAuthorized — needs sender + Merkle witness; today structural only
// ===========================================================================

#[test]
#[ignore = "blocked on caveat-correctness lane: executor wires MerkleMembership witness through WitnessedPredicateRegistry (CAVEAT-LAYER-COVERAGE.md §1 row 15)"]
fn executor_sender_authorized_with_membership_witness_accepts() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on caveat-correctness lane: SenderAuthorized rejects when sender not in set"]
fn executor_sender_authorized_rejects_non_member() {
    panic!("blocked");
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
#[ignore = "blocked on caveat-correctness multi-cell-eval + γ.2 Phase 1 wiring (STAGE-7-GAMMA-2-PI-DESIGN.md, CAVEAT-LAYER-COVERAGE.md §1 row 24)"]
fn executor_bilateral_transfer_with_bound_delta_accepts() {
    // Two cells, each declaring BoundDelta { peer_cell = other, EqualAndOpposite }.
    // Transfer 10 from A to B. Executor must:
    //   1. Evaluate A's CellProgram against the transition (A's bal_lo -= 10).
    //   2. Evaluate B's CellProgram against the transition (B's bal_lo += 10).
    //   3. Run the γ.2 cross-cell match loop, confirming the deltas pair.
    // Until the multi-cell-eval lane lands, this test cannot pass.
    panic!("blocked");
}
