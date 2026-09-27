//! COORDINATION-TURN CLASS regression lock ("leash, not ledger").
//!
//! `ComputronCosts::coordination_exempt` (opt-in, default off) waives the
//! CHARGE for turns that are pure oversight traffic — EmitEvent-only, no
//! `balance_change` anywhere in the forest (`Turn::is_coordination`). The
//! computron stays a LEASH (metering is honest: receipts report the true
//! `computrons_used`) but stops being a LEDGER for the class (a `fee = 0`
//! coordination turn admits and commits, even from an UNFUNDED cell).
//!
//! Locked both ways:
//! - exempt=true : fee=0 EmitEvent-only turn COMMITS (even at balance 0);
//! - exempt=false: the same turn still REJECTS `BudgetExceeded` (legacy
//!   behavior is bit-identical when the flag is off — the upstream default);
//! - no leak     : a `Transfer` (economic) turn at fee=0 REJECTS even under
//!   exempt=true — the class cannot leak to value moves;
//! - honest leash: the exempted turn's receipt reports NONZERO
//!   `computrons_used`;
//! - admission mirror: `estimate_cost` / `validate_without_apply` agree with
//!   the execution path on both sides of the flag.

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, Event, TurnError,
    TurnExecutor,
    turn::{Turn, TurnResult},
};

fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn make_open_cell(seed: u8, balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

fn turn_with_effects(agent: CellId, effects: Vec<Effect>, fee: u64) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: agent,
        method: *blake3::hash(b"helm.chat").as_bytes(),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects,
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    });
    Turn {
        agent,
        nonce: 0,
        call_forest: forest,
        fee,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

/// An EmitEvent-only "chat" turn — the coordination shape.
fn chat_turn(agent: CellId, fee: u64) -> Turn {
    turn_with_effects(
        agent,
        vec![Effect::EmitEvent {
            cell: agent,
            event: Event::new(*blake3::hash(b"helm.chat").as_bytes(), vec![[7u8; 32]]),
        }],
        fee,
    )
}

/// A `Transfer` (economic) turn — must NEVER ride the exemption.
fn transfer_turn(agent: CellId, to: CellId, amount: u64, fee: u64) -> Turn {
    turn_with_effects(
        agent,
        vec![Effect::Transfer {
            from: agent,
            to,
            amount,
        }],
        fee,
    )
}

fn exempt_executor() -> TurnExecutor {
    let mut costs = ComputronCosts::default_costs();
    costs.coordination_exempt = true;
    TurnExecutor::new(costs)
}

#[test]
fn is_coordination_classifies() {
    let agent = make_open_cell(1, 0).id();
    let to = make_open_cell(2, 0).id();
    assert!(chat_turn(agent, 0).is_coordination());
    assert!(!transfer_turn(agent, to, 1, 0).is_coordination());
    // Mixed forest (EmitEvent + Transfer) is NOT coordination.
    let mixed = turn_with_effects(
        agent,
        vec![
            Effect::EmitEvent {
                cell: agent,
                event: Event::new([1u8; 32], vec![]),
            },
            Effect::Transfer {
                from: agent,
                to,
                amount: 1,
            },
        ],
        0,
    );
    assert!(!mixed.is_coordination());
    // A declared balance_change disqualifies even an EmitEvent-only action.
    let mut declared = chat_turn(agent, 0);
    declared.call_forest.roots[0].action.balance_change = Some(0);
    assert!(!declared.is_coordination());
    // A zero-effect action is still non-mutating: coordination.
    let no_effects = turn_with_effects(agent, vec![], 0);
    assert!(no_effects.is_coordination());
    // An EMPTY forest is NOT coordination (nothing to classify; the executor
    // rejects it as EmptyForest anyway).
    let mut empty = chat_turn(agent, 0);
    empty.call_forest = CallForest::new();
    assert!(!empty.is_coordination());
}

#[test]
fn zero_fee_chat_commits_when_exempt_even_unfunded() {
    let agent = make_open_cell(1, 0); // UNFUNDED — the class's whole point
    let agent_id = agent.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent).unwrap();

    let executor = exempt_executor();
    let turn = chat_turn(agent_id, 0);
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_committed(),
        "exempt fee=0 chat turn must commit: {result:?}"
    );
}

#[test]
fn zero_fee_chat_still_rejects_when_not_exempt() {
    // Regression lock the OTHER way: with the flag off (the upstream
    // default), behavior is exactly legacy — fee=0 cannot cover the metered
    // cost and the turn rejects BudgetExceeded.
    let agent = make_open_cell(1, 1_000_000);
    let agent_id = agent.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::default_costs());
    let turn = chat_turn(agent_id, 0);
    match executor.execute(&turn, &mut ledger) {
        TurnResult::Rejected {
            reason: TurnError::BudgetExceeded { .. },
            ..
        } => {}
        other => panic!("non-exempt fee=0 chat turn must reject BudgetExceeded, got {other:?}"),
    }
}

#[test]
fn zero_fee_transfer_rejects_even_when_exempt() {
    // NO LEAK: an economic turn cannot ride the coordination class.
    let agent = make_open_cell(1, 1_000_000);
    let recipient = make_open_cell(2, 0);
    let agent_id = agent.id();
    let recipient_id = recipient.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent).unwrap();
    ledger.insert_cell(recipient).unwrap();

    let executor = exempt_executor();
    let turn = transfer_turn(agent_id, recipient_id, 100, 0);
    match executor.execute(&turn, &mut ledger) {
        TurnResult::Rejected {
            reason: TurnError::BudgetExceeded { .. },
            ..
        } => {}
        other => panic!("fee=0 Transfer must reject even under exempt, got {other:?}"),
    }
}

#[test]
fn exempt_receipt_keeps_honest_computrons_used() {
    // The leash stays observable: only the CHARGE is waived, the metering is
    // real — the receipt must report the true nonzero cost.
    let agent = make_open_cell(1, 0);
    let agent_id = agent.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent).unwrap();

    let executor = exempt_executor();
    let turn = chat_turn(agent_id, 0);
    match executor.execute(&turn, &mut ledger) {
        TurnResult::Committed {
            receipt,
            computrons_used,
            ..
        } => {
            assert!(
                computrons_used > 0,
                "exempted turn must still METER (got 0 computrons_used)"
            );
            assert_eq!(
                receipt.computrons_used, computrons_used,
                "receipt must carry the same honest metering"
            );
        }
        other => panic!("expected commit, got {other:?}"),
    }
}

#[test]
fn estimate_and_validate_mirror_the_exemption() {
    let agent = make_open_cell(1, 0);
    let agent_id = agent.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent).unwrap();

    let exempt = exempt_executor();
    let legacy = TurnExecutor::new(ComputronCosts::default_costs());
    let chat = chat_turn(agent_id, 0);
    let transfer = transfer_turn(agent_id, make_open_cell(2, 0).id(), 1, 0);

    assert_eq!(exempt.estimate_cost(&chat), 0, "exempt coordination estimates 0");
    assert!(legacy.estimate_cost(&chat) > 0, "legacy estimate unchanged");
    assert!(
        exempt.estimate_cost(&transfer) > 0,
        "economic turns estimate real cost even under exempt"
    );

    assert!(
        exempt.validate_without_apply(&chat, &ledger).is_ok(),
        "exempt fee=0 coordination turn validates"
    );
    assert!(
        matches!(
            legacy.validate_without_apply(&chat, &ledger),
            Err(TurnError::BudgetExceeded { .. })
        ),
        "legacy fee=0 coordination turn fails validation"
    );
}

#[test]
fn exempt_turn_with_nonzero_fee_still_commits_and_charges() {
    // Opting in does not FORBID a fee: a funded cell may still attach one
    // (it is debited and distributed exactly as before).
    let agent = make_open_cell(1, 10_000);
    let agent_id = agent.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent).unwrap();

    let executor = exempt_executor();
    let turn = chat_turn(agent_id, 1_000);
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed(), "funded exempt turn commits: {result:?}");
    let balance = ledger.get(&agent_id).unwrap().state.balance();
    assert_eq!(
        balance, 9_000,
        "an attached fee is still debited (fee stays a real move when carried)"
    );
}
