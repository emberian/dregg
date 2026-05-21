//! Programmable Cell Demo
//!
//! Demonstrates cell programs (smart contracts):
//!
//! 1. Create a cell with a Predicate program (e.g., "balance must never go below 100")
//!    - Execute a turn that respects the predicate -> succeeds
//!    - Execute a turn that violates the predicate -> fails with clear error
//! 2. Create a cell with a Circuit program (hash of a verification circuit)
//!    - Show that only turns accompanied by a valid STARK proof can modify the cell
//!
//! Uses:
//! - `cell/src/program.rs` (CellProgram, StateConstraint)
//! - `turn/src/executor.rs` (TurnExecutor, ProofVerifier)

use pyana_cell::program::{CellProgram, ProgramError, StateConstraint, field_from_u64};
use pyana_cell::state::CellState;
use pyana_cell::{AuthRequired, Cell, Ledger, Permissions, VerificationKey};
use pyana_turn::action::symbol;
use pyana_turn::executor::{ComputronCosts, ProofVerifier, TurnExecutor};
use pyana_turn::forest::CallForest;
use pyana_turn::{Action, Authorization, DelegationMode, Effect, Turn, TurnResult};

/// A mock proof verifier that validates proofs based on a simple protocol:
/// The proof bytes must start with the verification key's first 4 bytes (matching check).
struct MockStarkVerifier;

impl ProofVerifier for MockStarkVerifier {
    fn verify(&self, proof: &[u8], _action: &str, _resource: &str, vk: &[u8]) -> bool {
        // Simple mock: proof is valid if it starts with the VK prefix (first 4 bytes).
        // In production this would be a real STARK/SNARK verifier.
        if proof.len() < 4 || vk.len() < 4 {
            return false;
        }
        proof[..4] == vk[..4]
    }
}

fn main() {
    println!("=== Pyana Programmable Cell Demo ===\n");

    // =========================================================================
    // SECTION 1: PREDICATE PROGRAMS
    // =========================================================================
    println!("--- Section 1: Predicate Programs ---\n");

    // Create a cell program that enforces:
    //   - field[0] (balance) must always be >= 100
    //   - field[1] (account_type) is immutable after creation
    //   - field[0] + field[2] must always equal 1000 (conservation)
    let predicate_program = CellProgram::Predicate(vec![
        StateConstraint::FieldGte {
            index: 0,
            value: field_from_u64(100),
        },
        StateConstraint::Immutable { index: 1 },
        StateConstraint::SumEquals {
            indices: vec![0, 2],
            value: field_from_u64(1000),
        },
    ]);

    println!("  Cell program constraints:");
    println!("    1. FieldGte(0, 100) -- balance must never go below 100");
    println!("    2. Immutable(1) -- account_type cannot change");
    println!("    3. SumEquals([0, 2], 1000) -- conservation law");
    println!();

    // Initialize the cell state.
    let mut cell_state = CellState::new(5000);
    cell_state.fields[0] = field_from_u64(800); // balance = 800
    cell_state.fields[1] = field_from_u64(42); // account_type = 42 (immutable)
    cell_state.fields[2] = field_from_u64(200); // reserve = 200 (800 + 200 = 1000)

    // Verify initial state satisfies the program.
    let init_result = predicate_program.evaluate(&cell_state, None);
    assert!(init_result.is_ok(), "Initial state must satisfy program");
    println!("  Initial state: balance=800, type=42, reserve=200");
    println!("  Program satisfied: [PASS]");
    println!();

    // --- Case 1A: Valid state transition (respects predicate) ---
    println!("  Case 1A: Valid withdrawal (balance stays above 100)");

    let old_state = cell_state.clone();
    let mut new_state = cell_state.clone();
    new_state.fields[0] = field_from_u64(500); // balance -> 500 (still >= 100)
    new_state.fields[2] = field_from_u64(500); // reserve -> 500 (500 + 500 = 1000)

    let result = predicate_program.evaluate(&new_state, Some(&old_state));
    assert!(result.is_ok());
    println!("    New state: balance=500, reserve=500");
    println!("    FieldGte(0, 100): 500 >= 100 [PASS]");
    println!("    Immutable(1): 42 == 42 [PASS]");
    println!("    SumEquals: 500 + 500 = 1000 [PASS]");
    println!("    Transition accepted: [PASS]");
    println!();

    // --- Case 1B: Invalid transition -- balance too low ---
    println!("  Case 1B: Invalid withdrawal (balance drops below 100)");

    let mut bad_state = cell_state.clone();
    bad_state.fields[0] = field_from_u64(50); // balance -> 50 (< 100!)
    bad_state.fields[2] = field_from_u64(950); // keep sum = 1000

    let result = predicate_program.evaluate(&bad_state, Some(&old_state));
    assert!(result.is_err());
    match result.unwrap_err() {
        ProgramError::ConstraintViolated { description, .. } => {
            println!("    Attempted: balance=50, reserve=950");
            println!("    REJECTED: {}", description);
        }
        other => println!("    REJECTED: {}", other),
    }
    println!();

    // --- Case 1C: Invalid transition -- immutable field changed ---
    println!("  Case 1C: Attempt to change immutable account_type");

    let mut tamper_state = cell_state.clone();
    tamper_state.fields[1] = field_from_u64(99); // try to change type

    let result = predicate_program.evaluate(&tamper_state, Some(&old_state));
    assert!(result.is_err());
    match result.unwrap_err() {
        ProgramError::ConstraintViolated { description, .. } => {
            println!("    Attempted: account_type 42 -> 99");
            println!("    REJECTED: {}", description);
        }
        other => println!("    REJECTED: {}", other),
    }
    println!();

    // --- Case 1D: Invalid transition -- conservation law violated ---
    println!("  Case 1D: Attempt to violate conservation law");

    let mut inflate_state = cell_state.clone();
    inflate_state.fields[0] = field_from_u64(900); // balance = 900
    inflate_state.fields[2] = field_from_u64(200); // reserve stays 200 -> sum = 1100 != 1000

    let result = predicate_program.evaluate(&inflate_state, Some(&old_state));
    assert!(result.is_err());
    match result.unwrap_err() {
        ProgramError::ConstraintViolated { description, .. } => {
            println!("    Attempted: balance=900, reserve=200 (sum=1100)");
            println!("    REJECTED: {}", description);
        }
        other => println!("    REJECTED: {}", other),
    }
    println!();

    // =========================================================================
    // SECTION 2: CIRCUIT PROGRAMS (ZK Proof Required)
    // =========================================================================
    println!("--- Section 2: Circuit Programs (STARK proof required) ---\n");

    // Create a cell whose state can only be modified with a valid STARK proof.
    // The circuit_hash identifies which verification circuit must be satisfied.
    let circuit_hash: [u8; 32] = *blake3::hash(b"pyana-balance-transfer-circuit-v1").as_bytes();
    let circuit_program = CellProgram::Circuit { circuit_hash };

    println!("  Circuit program:");
    println!(
        "    circuit_hash: {:02x}{:02x}{:02x}{:02x}...",
        circuit_hash[0], circuit_hash[1], circuit_hash[2], circuit_hash[3]
    );
    println!("    Requires: valid STARK proof matching verification key");
    println!();

    // Show that directly evaluating a circuit program demands a proof.
    let state = CellState::new(0);
    let result = circuit_program.evaluate(&state, None);
    assert!(result.is_err());
    match result.unwrap_err() {
        ProgramError::CircuitProofRequired { circuit_hash: h } => {
            println!("  Direct evaluation without proof:");
            println!("    REJECTED: circuit program requires proof");
            println!(
                "    Expected circuit: {:02x}{:02x}{:02x}{:02x}...",
                h[0], h[1], h[2], h[3]
            );
        }
        other => println!("    REJECTED: {}", other),
    }
    println!();

    // =========================================================================
    // SECTION 3: Full executor integration with proof verification
    // =========================================================================
    println!("--- Section 3: Executor integration ---\n");

    // Set up a ledger with a proof-protected cell.
    let agent_pubkey = [0xAA; 32];
    let token_id = [0x00; 32];

    // Create the agent cell (has balance to pay fees).
    let mut agent_cell = Cell::with_balance(agent_pubkey, token_id, 100_000);
    let agent_id = agent_cell.id;
    // Agent allows everything on itself (no auth required for any action).
    agent_cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };

    // Create the proof-protected target cell.
    let target_pubkey = [0xBB; 32];
    let mut target_cell = Cell::new(target_pubkey, token_id);
    let target_id = target_cell.id;
    target_cell.program = circuit_program.clone();
    // Requires Proof auth for state changes, None for access/receive.
    target_cell.permissions = Permissions {
        send: AuthRequired::Proof,
        receive: AuthRequired::None,
        set_state: AuthRequired::Proof,
        set_permissions: AuthRequired::Proof,
        set_verification_key: AuthRequired::Proof,
        increment_nonce: AuthRequired::Proof,
        delegate: AuthRequired::Proof,
        access: AuthRequired::None,
    };
    // Set a verification key that the mock verifier will check against.
    let vk_data = b"proof-circuit-vk-data-v1".to_vec();
    target_cell.verification_key = Some(VerificationKey::new(vk_data.clone()));
    // Give the agent a capability to access the target cell (no auth required to exercise).
    agent_cell.capabilities.grant(target_id, AuthRequired::None);

    // Insert both cells into the ledger.
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent_cell).unwrap();
    ledger.insert_cell(target_cell).unwrap();

    // Create the executor with our mock proof verifier.
    let mut executor = TurnExecutor::with_proof_verifier(
        ComputronCosts::default_costs(),
        Box::new(MockStarkVerifier),
    );
    executor.set_timestamp(1700000000);

    println!("  Ledger setup:");
    println!("    Agent cell: {:?} (balance: 100,000)", agent_id);
    println!("    Target cell: {:?} (proof-protected)", target_id);
    println!();

    // --- Case 3A: Turn WITHOUT proof (rejected) ---
    println!("  Case 3A: Turn without proof authorization");

    let action_no_proof = Action {
        target: target_id,
        method: symbol("set_state"),
        args: vec![],
        authorization: Authorization::None,
        preconditions: Default::default(),
        effects: vec![Effect::SetField {
            cell: target_id,
            index: 0,
            value: field_from_u64(999),
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
    };

    let turn_no_proof = Turn {
        agent: agent_id,
        nonce: 0,
        fee: 5000,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: Vec::new(),
        call_forest: {
            let mut f = CallForest::new();
            f.add_root(action_no_proof);
            f
        },
    };

    let result = executor.execute(&turn_no_proof, &mut ledger);
    match &result {
        TurnResult::Rejected { reason, .. } => {
            println!("    REJECTED: {}", reason);
            println!("    (Cell requires Proof authorization for SetState)");
        }
        TurnResult::Committed { .. } => {
            panic!("Should have been rejected!");
        }
        _ => panic!("Unexpected turn result"),
    }
    println!();

    // Reset the agent's nonce and balance for the next test.
    // (The fee was already deducted even on rejection.)
    let agent = ledger.get_mut(&agent_id).unwrap();
    agent.state.nonce = 0;
    agent.state.balance = 100_000;

    // --- Case 3B: Turn WITH valid proof (accepted) ---
    println!("  Case 3B: Turn with valid STARK proof");

    // Construct a proof that passes our mock verifier.
    // The mock verifier checks that proof[..4] == vk.data[..4].
    let mut valid_proof = vec![0u8; 128]; // 128-byte simulated STARK proof
    valid_proof[..4].copy_from_slice(&vk_data[..4]); // Match VK data prefix
    // Fill rest with "proof data"
    for i in 4..128 {
        valid_proof[i] = (i as u8).wrapping_mul(7);
    }

    let action_with_proof = Action {
        target: target_id,
        method: symbol("set_state"),
        args: vec![],
        authorization: Authorization::Proof {
            proof_bytes: valid_proof.clone(),
            bound_action: "set_state".to_string(),
            bound_resource: String::new(),
        },
        preconditions: Default::default(),
        effects: vec![Effect::SetField {
            cell: target_id,
            index: 0,
            value: field_from_u64(42),
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
    };

    let turn_with_proof = Turn {
        agent: agent_id,
        nonce: 0,
        fee: 5000,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: Vec::new(),
        call_forest: {
            let mut f = CallForest::new();
            f.add_root(action_with_proof);
            f
        },
    };

    let result = executor.execute(&turn_with_proof, &mut ledger);
    match &result {
        TurnResult::Committed {
            receipt,
            computrons_used,
            ..
        } => {
            println!("    ACCEPTED: turn committed successfully");
            println!("    Computrons used: {}", computrons_used);
            println!(
                "    Post-state hash: {:02x}{:02x}{:02x}{:02x}...",
                receipt.post_state_hash[0],
                receipt.post_state_hash[1],
                receipt.post_state_hash[2],
                receipt.post_state_hash[3]
            );
        }
        TurnResult::Rejected { reason, .. } => {
            panic!("Should have been accepted, got: {}", reason);
        }
        _ => panic!("Unexpected turn result"),
    }
    println!();

    // Verify the state was actually updated.
    let target_after = ledger.get(&target_id).unwrap();
    let field_val = u64::from_le_bytes(target_after.state.fields[0][..8].try_into().unwrap());
    assert_eq!(field_val, 42);
    println!("    Target cell field[0] after: {} [correct]", field_val);
    println!();

    // --- Case 3C: Turn with INVALID proof (rejected) ---
    println!("  Case 3C: Turn with invalid proof (wrong VK prefix)");

    // Reset for next test.
    let agent = ledger.get_mut(&agent_id).unwrap();
    let current_nonce = agent.state.nonce;

    let mut invalid_proof = vec![0u8; 128];
    invalid_proof[..4].copy_from_slice(&[0xDE, 0xAD, 0xBE, 0xEF]); // Wrong prefix
    for i in 4..128 {
        invalid_proof[i] = (i as u8).wrapping_mul(13);
    }

    let action_bad_proof = Action {
        target: target_id,
        method: symbol("set_state"),
        args: vec![],
        authorization: Authorization::Proof {
            proof_bytes: invalid_proof,
            bound_action: "set_state".to_string(),
            bound_resource: String::new(),
        },
        preconditions: Default::default(),
        effects: vec![Effect::SetField {
            cell: target_id,
            index: 0,
            value: field_from_u64(9999),
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
    };

    let turn_bad_proof = Turn {
        agent: agent_id,
        nonce: current_nonce,
        fee: 5000,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: Vec::new(),
        call_forest: {
            let mut f = CallForest::new();
            f.add_root(action_bad_proof);
            f
        },
    };

    let result = executor.execute(&turn_bad_proof, &mut ledger);
    match &result {
        TurnResult::Rejected { reason, .. } => {
            println!("    REJECTED: {}", reason);
            println!("    (Proof verification failed -- VK mismatch)");
        }
        TurnResult::Committed { .. } => {
            panic!("Should have been rejected!");
        }
        _ => panic!("Unexpected turn result"),
    }

    // Confirm state was NOT modified (atomicity).
    let target_after = ledger.get(&target_id).unwrap();
    let field_val = u64::from_le_bytes(target_after.state.fields[0][..8].try_into().unwrap());
    assert_eq!(field_val, 42, "State must not change on rejected turn");
    println!(
        "    Target cell field[0] unchanged: {} [atomicity preserved]",
        field_val
    );
    println!();

    // =========================================================================
    // SUMMARY
    // =========================================================================
    println!("--- Summary ---\n");
    println!("  Predicate programs enforce invariants on every state transition:");
    println!("    - Minimum balance thresholds (FieldGte)");
    println!("    - Immutable identity fields (Immutable)");
    println!("    - Conservation laws (SumEquals)");
    println!();
    println!("  Circuit programs require cryptographic authorization:");
    println!("    - Only a valid STARK proof (matching the cell's VK) can modify state");
    println!("    - Invalid or absent proofs are rejected atomically");
    println!("    - The circuit_hash identifies which verification logic applies");
    println!();
    println!("=== Programmable Cell Demo Complete ===");
}
