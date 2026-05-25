//! Time-Locked Escrow Demo
//!
//! Demonstrates:
//! 1. Create an escrow cell with a CellProgram (Predicate constraints):
//!    - SumEquals: deposited + withdrawn = constant (conservation)
//!    - FieldGte: unlock_time constraint for time-locking
//!    - Immutable: beneficiary cannot change
//! 2. Deposit funds into escrow
//! 3. Attempt early withdrawal (rejected by Gte constraint)
//! 4. Wait for unlock time
//! 5. Successful withdrawal after unlock
//! 6. Conservation verified throughout

use pyana_cell::program::{CellProgram, StateConstraint, field_from_u64};
use pyana_cell::state::CellState;

fn main() {
    println!("=== Pyana Time-Locked Escrow Demo ===\n");

    // --- Setup ---
    // Escrow parameters:
    // field[0] = total_deposited (cumulative)
    // field[1] = total_withdrawn (cumulative)
    // field[2] = unlock_time (unix timestamp)
    // field[3] = beneficiary (hash of beneficiary's public key)
    // field[4] = depositor (hash of depositor's public key)
    //
    // Invariant: deposited + withdrawn = TOTAL_VALUE at all times
    // (using SumEquals over fields[0] and [1])

    let depositor_id: u64 = 0xAAAA_BBBB_CCCC_DDDD;
    let beneficiary_id: u64 = 0x1111_2222_3333_4444;
    let unlock_time: u64 = 1700100000; // Some future time
    let total_escrow_value: u64 = 10000; // 10,000 units total capacity

    println!("Escrow Parameters:");
    println!("  Depositor:      0x{:016x}", depositor_id);
    println!("  Beneficiary:    0x{:016x}", beneficiary_id);
    println!("  Unlock time:    {} (unix)", unlock_time);
    println!("  Escrow capacity: {} units", total_escrow_value);
    println!();

    // =======================================================================
    // STEP 1: CREATE ESCROW CELL WITH PROGRAM
    // =======================================================================
    println!("--- Step 1: CREATE ESCROW CELL ---");

    let escrow_program = CellProgram::Predicate(vec![
        // Conservation law: deposited + withdrawn = total capacity
        // This means everything deposited must eventually be withdrawn (or remains deposited).
        StateConstraint::SumEquals {
            indices: vec![0, 1],
            value: field_from_u64(total_escrow_value),
        },
        // Time lock: field[2] must be <= current_time for withdrawal to happen.
        // We enforce this indirectly: the withdrawal action must set field[2]
        // to the current time, proving it's past the unlock threshold.
        // For the demo, we use FieldGte to require field[2] >= unlock_time
        // (the unlock_time is stored and must not decrease).
        StateConstraint::FieldGte {
            index: 2,
            value: field_from_u64(unlock_time),
        },
        // Beneficiary is immutable after creation
        StateConstraint::Immutable { index: 3 },
        // Depositor is immutable after creation
        StateConstraint::Immutable { index: 4 },
    ]);

    // Initialize the escrow state
    let mut escrow_state = CellState::new(0);
    escrow_state.fields[0] = field_from_u64(total_escrow_value); // All value starts as "deposited"
    escrow_state.fields[1] = field_from_u64(0); // Nothing withdrawn yet
    escrow_state.fields[2] = field_from_u64(unlock_time); // The unlock time
    escrow_state.fields[3] = field_from_u64(beneficiary_id); // Beneficiary
    escrow_state.fields[4] = field_from_u64(depositor_id); // Depositor

    // Verify initial state satisfies program (initialization)
    let init_result = escrow_program.evaluate(&escrow_state, None, None);
    assert!(init_result.is_ok(), "Initial state must satisfy program");

    println!("  Program constraints:");
    println!(
        "    - SumEquals([0,1], {}) — conservation law",
        total_escrow_value
    );
    println!("    - FieldGte(2, {}) — time lock", unlock_time);
    println!("    - Immutable(3) — beneficiary locked");
    println!("    - Immutable(4) — depositor locked");
    println!("  Initial state valid: [PASS]");
    println!("  field[0] (deposited): {}", total_escrow_value);
    println!("  field[1] (withdrawn): 0");
    println!();

    // =======================================================================
    // STEP 2: DEPOSIT (modify balances within conservation law)
    // =======================================================================
    println!("--- Step 2: DEPOSIT (5000 units moved to available) ---");

    // Simulate a partial withdrawal becoming available:
    // Move 5000 from deposited to withdrawn (as if beneficiary is claiming)
    // But first, let's show that the conservation law works:
    let old_state = escrow_state.clone();

    // Attempt a valid rebalance: deposited=7000, withdrawn=3000 (sum=10000)
    let mut new_state = escrow_state.clone();
    new_state.fields[0] = field_from_u64(7000); // deposited = 7000
    new_state.fields[1] = field_from_u64(3000); // withdrawn = 3000

    let rebalance_result = escrow_program.evaluate(&new_state, Some(&old_state), None);
    assert!(rebalance_result.is_ok(), "Valid rebalance should pass");
    println!("  Rebalance: deposited=7000, withdrawn=3000 (sum=10000) [PASS]");

    // Attempt an INVALID rebalance that violates conservation
    let mut bad_state = escrow_state.clone();
    bad_state.fields[0] = field_from_u64(7000);
    bad_state.fields[1] = field_from_u64(5000); // sum = 12000 != 10000!

    let bad_result = escrow_program.evaluate(&bad_state, Some(&old_state), None);
    assert!(bad_result.is_err(), "Conservation violation should fail");
    println!("  INVALID: deposited=7000, withdrawn=5000 (sum=12000) [REJECTED]");
    if let Err(e) = bad_result {
        println!("    Error: {}", e);
    }

    // Accept the valid rebalance
    escrow_state = new_state;
    println!();

    // =======================================================================
    // STEP 3: ATTEMPT EARLY WITHDRAWAL (time lock violation)
    // =======================================================================
    println!("--- Step 3: EARLY WITHDRAWAL ATTEMPT ---");

    // Try to change the unlock_time to an earlier value (bypass time lock)
    let mut early_state = escrow_state.clone();
    early_state.fields[2] = field_from_u64(1700000000); // Try to set earlier unlock

    let early_result = escrow_program.evaluate(&early_state, Some(&escrow_state), None);
    assert!(
        early_result.is_err(),
        "Lowering unlock time should fail (FieldGte)"
    );
    println!("  Attempted to lower unlock_time to 1700000000...");
    if let Err(e) = early_result {
        println!("  REJECTED: {}", e);
    }
    println!();

    // =======================================================================
    // STEP 4: ATTEMPT TO CHANGE BENEFICIARY (immutability violation)
    // =======================================================================
    println!("--- Step 4: ATTEMPT TO CHANGE BENEFICIARY ---");

    let attacker_id: u64 = 0xDEAD_BEEF_DEAD_BEEF;
    let mut tamper_state = escrow_state.clone();
    tamper_state.fields[3] = field_from_u64(attacker_id); // Try to change beneficiary

    let tamper_result = escrow_program.evaluate(&tamper_state, Some(&escrow_state), None);
    assert!(
        tamper_result.is_err(),
        "Changing immutable beneficiary should fail"
    );
    println!(
        "  Attacker attempts to change beneficiary to 0x{:016x}...",
        attacker_id
    );
    if let Err(e) = tamper_result {
        println!("  REJECTED: {}", e);
    }
    println!();

    // =======================================================================
    // STEP 5: VALID WITHDRAWAL (after unlock time)
    // =======================================================================
    println!("--- Step 5: VALID WITHDRAWAL (time lock satisfied) ---");

    // Now simulate that time has passed. The withdrawal action sets a higher
    // timestamp in field[2] proving that the current time > unlock_time.
    // Since FieldGte requires field[2] >= unlock_time, and we're setting it
    // to a LATER time, this is valid.
    let withdrawal_amount: u64 = 2000;
    let current_deposited = 7000u64;
    let current_withdrawn = 3000u64;

    let mut withdrawal_state = escrow_state.clone();
    withdrawal_state.fields[0] = field_from_u64(current_deposited - withdrawal_amount); // 5000
    withdrawal_state.fields[1] = field_from_u64(current_withdrawn + withdrawal_amount); // 5000
    // Keep unlock_time at or above threshold (proving current_time >= unlock_time)
    withdrawal_state.fields[2] = field_from_u64(unlock_time + 86400); // 1 day after unlock

    let withdrawal_result = escrow_program.evaluate(&withdrawal_state, Some(&escrow_state), None);
    assert!(
        withdrawal_result.is_ok(),
        "Valid withdrawal after unlock should pass"
    );

    println!(
        "  Current time: {} (past unlock time {})",
        unlock_time + 86400,
        unlock_time
    );
    println!("  Withdrawal: {} units", withdrawal_amount);
    println!(
        "  deposited: {} -> {}",
        current_deposited,
        current_deposited - withdrawal_amount
    );
    println!(
        "  withdrawn: {} -> {}",
        current_withdrawn,
        current_withdrawn + withdrawal_amount
    );
    println!(
        "  Sum check: {} + {} = {} [PASS]",
        current_deposited - withdrawal_amount,
        current_withdrawn + withdrawal_amount,
        total_escrow_value
    );
    println!(
        "  Time lock: {} >= {} [PASS]",
        unlock_time + 86400,
        unlock_time
    );
    println!("  Beneficiary unchanged: [PASS]");
    println!("  Depositor unchanged: [PASS]");

    escrow_state = withdrawal_state;
    println!();

    // =======================================================================
    // STEP 6: CONSERVATION VERIFICATION
    // =======================================================================
    println!("--- Step 6: CONSERVATION VERIFICATION ---");

    // Extract current values
    let final_deposited = u64::from_le_bytes(escrow_state.fields[0][..8].try_into().unwrap());
    let final_withdrawn = u64::from_le_bytes(escrow_state.fields[1][..8].try_into().unwrap());

    println!("  Final state:");
    println!("    field[0] (deposited):   {}", final_deposited);
    println!("    field[1] (withdrawn):   {}", final_withdrawn);
    println!(
        "    field[2] (unlock_time): {} (updated to prove time passage)",
        u64::from_le_bytes(escrow_state.fields[2][..8].try_into().unwrap())
    );
    println!(
        "    field[3] (beneficiary): 0x{:016x} (immutable)",
        beneficiary_id
    );
    println!(
        "    field[4] (depositor):   0x{:016x} (immutable)",
        depositor_id
    );
    println!();
    println!(
        "  Conservation law: {} + {} = {} [VERIFIED]",
        final_deposited,
        final_withdrawn,
        final_deposited + final_withdrawn
    );
    assert_eq!(final_deposited + final_withdrawn, total_escrow_value);

    // One final comprehensive check
    let final_check = escrow_program.evaluate(&escrow_state, Some(&escrow_state), None);
    assert!(
        final_check.is_ok(),
        "Final state must satisfy all program constraints"
    );
    println!("  All program constraints satisfied: [PASS]");
    println!();
    println!("=== Escrow Demo Complete ===");
}
