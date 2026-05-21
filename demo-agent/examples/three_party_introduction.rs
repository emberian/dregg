//! Three-Party Introduction Demo
//!
//! Demonstrates the ocap three-party introduction pattern:
//!
//! 1. Alice, Bob, Carol are three cells in a ledger.
//! 2. Alice holds capabilities to both Bob and Carol.
//! 3. Alice introduces Bob to Carol (grants Bob a cap to Carol).
//! 4. Bob can now act on Carol (verified via c-list).
//! 5. Eve tries to reach Carol without introduction -- fails.
//! 6. Transitive introduction: Bob introduces Dave to Carol.
//!
//! This is the fundamental mechanism for controlled capability propagation
//! in an ocap system: you can only gain access through introduction by
//! someone who already holds both ends of the relationship.

use pyana_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use pyana_turn::{TurnBuilder, TurnExecutor, ComputronCosts, TurnResult};

/// Create a cell with open permissions and a given balance.
fn make_open_cell(seed: u8, balance: u64) -> Cell {
    let mut key = [0u8; 32];
    key[0] = seed;
    let token_id = [0u8; 32];
    let mut cell = Cell::with_balance(key, token_id, balance);
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
    cell
}

fn short_id(id: &CellId) -> String {
    let b = id.as_bytes();
    format!("{:02x}{:02x}{:02x}{:02x}", b[0], b[1], b[2], b[3])
}

fn main() {
    println!("=== Pyana Three-Party Introduction Demo ===");
    println!("    Object-Capability Introduction Pattern");
    println!();

    // =========================================================================
    // SETUP: Create cells
    // =========================================================================
    println!("--- Setup: Create cells ---");
    println!();

    let alice = make_open_cell(0xAA, 50000);
    let bob = make_open_cell(0xBB, 10000);
    let carol = make_open_cell(0xCC, 10000);
    let dave = make_open_cell(0xDD, 10000);
    let eve = make_open_cell(0xEE, 10000);

    let alice_id = alice.id;
    let bob_id = bob.id;
    let carol_id = carol.id;
    let dave_id = dave.id;
    let eve_id = eve.id;

    println!("  Alice: {} (the introducer)", short_id(&alice_id));
    println!("  Bob:   {} (will be introduced to Carol)", short_id(&bob_id));
    println!("  Carol: {} (the target)", short_id(&carol_id));
    println!("  Dave:  {} (will be transitively introduced)", short_id(&dave_id));
    println!("  Eve:   {} (unauthorized -- no introduction)", short_id(&eve_id));
    println!();

    // =========================================================================
    // STEP 1: Set up initial capabilities
    // =========================================================================
    println!("--- Step 1: Initial capability setup ---");
    println!();

    let mut ledger = Ledger::new();

    // Alice gets caps to Bob, Carol, and Dave.
    let mut alice_cell = alice;
    alice_cell.capabilities.grant(bob_id, AuthRequired::None);
    alice_cell.capabilities.grant(carol_id, AuthRequired::None);
    alice_cell.capabilities.grant(dave_id, AuthRequired::None);

    // Eve gets a cap to herself only (no introductions).
    let eve_cell = eve;

    ledger.insert_cell(alice_cell).unwrap();
    ledger.insert_cell(bob).unwrap();
    ledger.insert_cell(carol).unwrap();
    ledger.insert_cell(dave).unwrap();
    ledger.insert_cell(eve_cell).unwrap();

    println!("  Alice's c-list: [Bob, Carol, Dave]");
    println!("  Bob's c-list:   [] (empty -- cannot reach Carol yet)");
    println!("  Eve's c-list:   [] (empty -- cannot reach anyone)");
    println!();

    // Verify Bob cannot reach Carol yet.
    let bob_cell = ledger.get(&bob_id).unwrap();
    assert!(!bob_cell.capabilities.has_access(&carol_id));
    println!("  Verified: Bob has NO access to Carol");
    println!();

    let executor = TurnExecutor::new(ComputronCosts::zero());

    // =========================================================================
    // STEP 2: Alice introduces Bob to Carol
    // =========================================================================
    println!("--- Step 2: Alice introduces Bob to Carol ---");
    println!();

    let mut builder = TurnBuilder::new(alice_id, 0);
    {
        let action = builder.action(alice_id, "introduce_bob_to_carol");
        action.introduce(alice_id, bob_id, carol_id, AuthRequired::None);
    }
    let turn = builder.fee(0).build();

    let result = executor.execute(&turn, &mut ledger);
    match &result {
        TurnResult::Committed { receipt, .. } => {
            println!("  Turn committed successfully!");
            println!("  Routing directives emitted: {}", receipt.routing_directives.len());
            for rd in &receipt.routing_directives {
                println!("    {} -> {} (authorized by turn {:02x}{:02x}...)",
                    short_id(&rd.sender),
                    short_id(&rd.target),
                    rd.authorizing_turn[0],
                    rd.authorizing_turn[1],
                );
            }
        }
        TurnResult::Rejected { reason, .. } => {
            panic!("Introduction failed: {}", reason);
        }
    }
    println!();

    // Verify Bob now has access to Carol.
    let bob_cell = ledger.get(&bob_id).unwrap();
    assert!(bob_cell.capabilities.has_access(&carol_id));
    println!("  Verified: Bob NOW has access to Carol!");
    println!("  Bob's c-list: [Carol]");
    println!();

    // =========================================================================
    // STEP 3: Eve tries to reach Carol without introduction -- FAILS
    // =========================================================================
    println!("--- Step 3: Eve tries to reach Carol (should FAIL) ---");
    println!();

    // Eve tries to introduce herself to Carol (she has no cap to Carol or Bob).
    let mut builder = TurnBuilder::new(eve_id, 0);
    {
        let action = builder.action(eve_id, "self_introduce");
        action.introduce(eve_id, eve_id, carol_id, AuthRequired::None);
    }
    let turn = builder.fee(0).build();

    let result = executor.execute(&turn, &mut ledger);
    match &result {
        TurnResult::Rejected { reason, .. } => {
            println!("  REJECTED (as expected): {}", reason);
        }
        TurnResult::Committed { .. } => {
            panic!("Should have been rejected!");
        }
    }
    println!();

    // Verify Eve still has no access to Carol.
    let eve_cell = ledger.get(&eve_id).unwrap();
    assert!(!eve_cell.capabilities.has_access(&carol_id));
    println!("  Verified: Eve still has NO access to Carol");
    println!("  The ocap discipline holds: no capability without introduction.");
    println!();

    // =========================================================================
    // STEP 4: Bob introduces Dave to Carol (transitive introduction)
    // =========================================================================
    println!("--- Step 4: Transitive introduction -- Bob introduces Dave to Carol ---");
    println!();
    println!("  Bob gained access to Carol in Step 2.");
    println!("  Now we give Bob a cap to Dave, and Bob can introduce Dave to Carol.");
    println!();

    // First, give Bob a cap to Dave (Alice does this).
    let mut builder = TurnBuilder::new(alice_id, 1);
    {
        let action = builder.action(alice_id, "introduce_bob_to_dave");
        action.introduce(alice_id, bob_id, dave_id, AuthRequired::None);
    }
    let turn = builder.fee(0).build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed(), "Alice introducing Bob to Dave should work");
    println!("  Alice introduced Bob to Dave (so Bob has [Carol, Dave])");

    // Now Bob introduces Dave to Carol.
    let mut builder = TurnBuilder::new(bob_id, 0);
    {
        let action = builder.action(bob_id, "introduce_dave_to_carol");
        action.introduce(bob_id, dave_id, carol_id, AuthRequired::None);
    }
    let turn = builder.fee(0).build();

    let result = executor.execute(&turn, &mut ledger);
    match &result {
        TurnResult::Committed { receipt, .. } => {
            println!("  Bob's transitive introduction succeeded!");
            println!("  Routing directives: {}", receipt.routing_directives.len());
            for rd in &receipt.routing_directives {
                println!("    {} -> {}",
                    short_id(&rd.sender),
                    short_id(&rd.target),
                );
            }
        }
        TurnResult::Rejected { reason, .. } => {
            panic!("Transitive introduction failed: {}", reason);
        }
    }
    println!();

    // Verify Dave now has access to Carol.
    let dave_cell = ledger.get(&dave_id).unwrap();
    assert!(dave_cell.capabilities.has_access(&carol_id));
    println!("  Verified: Dave NOW has access to Carol!");
    println!("  Dave's c-list: [Carol]");
    println!();

    // =========================================================================
    // STEP 5: Demonstrate attenuation -- Alice introduces with restricted perms
    // =========================================================================
    println!("--- Step 5: Attenuated introduction ---");
    println!();
    println!("  Alice can introduce with LESS permission than she holds.");
    println!("  Alice holds None (unrestricted) access to Carol.");
    println!("  She introduces Dave to Carol with Signature-only access.");
    println!();

    // Give Alice a fresh cell to introduce (reuse dave for simplicity - already has access,
    // but we can demonstrate by checking the permission level of a new grant).
    // Instead, let's create a new cell for this step.
    let frank = make_open_cell(0xFF, 5000);
    let frank_id = frank.id;
    ledger.insert_cell(frank).unwrap();

    // Give Alice a cap to Frank.
    let alice_cell = ledger.get_mut(&alice_id).unwrap();
    alice_cell.capabilities.grant(frank_id, AuthRequired::None);

    let mut builder = TurnBuilder::new(alice_id, 2);
    {
        let action = builder.action(alice_id, "introduce_frank_attenuated");
        // Grant Frank access to Carol, but only with Signature-level permissions.
        action.introduce(alice_id, frank_id, carol_id, AuthRequired::Signature);
    }
    let turn = builder.fee(0).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed(), "attenuated introduction should succeed");
    println!("  Alice introduced Frank to Carol with Signature-only access.");

    let frank_cell = ledger.get(&frank_id).unwrap();
    let cap = frank_cell.capabilities.lookup_by_target(&carol_id).unwrap();
    assert_eq!(cap.permissions, AuthRequired::Signature);
    println!("  Verified: Frank's cap to Carol requires Signature auth.");
    println!("  (Alice holds None/unrestricted, so Signature is a valid attenuation.)");
    println!();

    // =========================================================================
    // STEP 6: Demonstrate amplification denial
    // =========================================================================
    println!("--- Step 6: Amplification denied ---");
    println!();
    println!("  Frank holds Signature-level access to Carol.");
    println!("  Frank tries to introduce Eve to Carol with None (wider) access.");
    println!("  This MUST fail: you cannot grant more than you hold.");
    println!();

    // Give Frank a cap to Eve.
    let frank_cell = ledger.get_mut(&frank_id).unwrap();
    frank_cell.capabilities.grant(eve_id, AuthRequired::None);

    let mut builder = TurnBuilder::new(frank_id, 0);
    {
        let action = builder.action(frank_id, "amplification_attempt");
        // Frank tries to grant Eve unrestricted access to Carol,
        // but Frank only has Signature-level access.
        action.introduce(frank_id, eve_id, carol_id, AuthRequired::None);
    }
    let turn = builder.fee(0).build();

    let result = executor.execute(&turn, &mut ledger);
    match &result {
        TurnResult::Rejected { reason, .. } => {
            println!("  REJECTED (as expected): {}", reason);
        }
        TurnResult::Committed { .. } => {
            panic!("Amplification should have been denied!");
        }
    }
    println!();

    // Verify Eve still has no access to Carol.
    let eve_cell = ledger.get(&eve_id).unwrap();
    assert!(!eve_cell.capabilities.has_access(&carol_id));
    println!("  Verified: Eve still has NO access to Carol.");
    println!("  Amplification is impossible: the attenuation-only rule holds.");
    println!();

    // =========================================================================
    // SUMMARY
    // =========================================================================
    println!("--- Summary: Security Properties ---");
    println!();
    println!("  [x] INTRODUCTION REQUIRED: Cells cannot gain capabilities without");
    println!("      being introduced by someone who already holds both ends.");
    println!();
    println!("  [x] ATTENUATION ONLY: An introducer can grant at most the same");
    println!("      permission level they hold. Never wider (no amplification).");
    println!();
    println!("  [x] TRANSITIVITY: Once introduced, a cell can itself introduce");
    println!("      others (subject to the same attenuation rules).");
    println!();
    println!("  [x] ROUTING DIRECTIVES: Each introduction emits a RoutingDirective");
    println!("      in the turn receipt, enabling the network layer to update routes.");
    println!();
    println!("  [x] FAIL-CLOSED: Without a valid capability chain, all access is denied.");
    println!();
    println!("=== Three-Party Introduction Demo Complete ===");
}
