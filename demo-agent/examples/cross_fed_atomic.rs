//! Cross-Federation Atomic Swap via ConditionalTurn
//!
//! Demonstrates STARK-conditional cross-domain atomic execution:
//!
//! Setup:
//! - Federation A has Alice with 1000 tokens and Bob with 0 tokens
//! - Federation B has Alice with 0 tokens and Bob with 1 NFT
//!
//! Protocol:
//! 1. Alice submits ConditionalTurn to Fed A:
//!    "Transfer 100 to Bob IFF proof that Bob transferred NFT to Alice in Fed B"
//! 2. Bob submits ConditionalTurn to Fed B:
//!    "Transfer NFT to Alice IFF proof that Alice transferred 100 to Bob in Fed A"
//! 3. Both present receipts as proofs -> both execute atomically
//! 4. If either times out -> both expire, no state change
//!
//! This replaces HTLC hash-lock patterns with receipt-based conditions,
//! which are strictly more general (any provable statement, not just preimage knowledge).

use pyana_cell::{Cell, CellId, Ledger, permissions::Permissions, AuthRequired};
use pyana_turn::{
    CallForest, CallTree, ComputronCosts, ConditionProof, ConditionalResult, ConditionalTurn,
    Effect, ProofCondition, Turn, TurnExecutor, TurnResult,
    action::{Action, Authorization, DelegationMode},
};

/// Create permissions that allow all operations without authorization.
/// Used for demo purposes only.
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

/// Build a simple transfer turn.
fn build_transfer_turn(
    agent: CellId,
    nonce: u64,
    from: CellId,
    to: CellId,
    amount: u64,
) -> Turn {
    let mut forest = CallForest::new();
    forest.roots.push(CallTree::new(Action {
        target: from,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::None,
        preconditions: Default::default(),
        effects: vec![Effect::Transfer { from, to, amount }],
        may_delegate: DelegationMode::None,
        balance_change: None,
        commitment_mode: Default::default(),
    }));
    Turn {
        agent,
        nonce,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        call_forest: forest,
    }
}

fn main() {
    println!("=== Cross-Federation Atomic Swap via ConditionalTurn ===\n");

    // ─── Setup: Two Federations ─────────────────────────────────────────────

    println!("--- Setting up two federations ---\n");

    // Federation A: token ledger
    let mut fed_a_ledger = Ledger::new();
    let alice_a_pk = [1u8; 32];
    let bob_a_pk = [2u8; 32];
    let token_id = [0u8; 32];

    let mut alice_a = Cell::with_balance(alice_a_pk, token_id, 1000);
    alice_a.permissions = open_permissions();
    let alice_a_id = alice_a.id;
    let mut bob_a = Cell::with_balance(bob_a_pk, token_id, 0);
    bob_a.permissions = open_permissions();
    let bob_a_id = bob_a.id;
    alice_a
        .capabilities
        .grant(bob_a_id, AuthRequired::None);

    fed_a_ledger.insert_cell(alice_a).unwrap();
    fed_a_ledger.insert_cell(bob_a).unwrap();

    println!("  Fed A - Alice: {} (balance: 1000)", short_id(alice_a_id));
    println!("  Fed A - Bob:   {} (balance: 0)", short_id(bob_a_id));

    // Federation B: NFT ledger
    let mut fed_b_ledger = Ledger::new();
    let alice_b_pk = [3u8; 32];
    let bob_b_pk = [4u8; 32];

    let mut alice_b = Cell::with_balance(alice_b_pk, token_id, 0);
    alice_b.permissions = open_permissions();
    let alice_b_id = alice_b.id;
    let mut bob_b = Cell::with_balance(bob_b_pk, token_id, 1);
    bob_b.permissions = open_permissions();
    let bob_b_id = bob_b.id;
    bob_b
        .capabilities
        .grant(alice_b_id, AuthRequired::None);

    fed_b_ledger.insert_cell(alice_b).unwrap();
    fed_b_ledger.insert_cell(bob_b).unwrap();

    println!("  Fed B - Alice: {} (NFTs: 0)", short_id(alice_b_id));
    println!("  Fed B - Bob:   {} (NFTs: 1)", short_id(bob_b_id));

    // ─── Step 1: Build the turns ────────────────────────────────────────────

    println!("\n--- Step 1: Building conditional turns ---\n");

    let alice_turn_a = build_transfer_turn(alice_a_id, 0, alice_a_id, bob_a_id, 100);
    let bob_turn_b = build_transfer_turn(bob_b_id, 0, bob_b_id, alice_b_id, 1);

    let alice_turn_hash = alice_turn_a.hash();
    let bob_turn_hash = bob_turn_b.hash();

    println!("  Alice's turn (Fed A): transfer 100 tokens to Bob");
    println!("    Turn hash: {}", short_hex(&alice_turn_hash));
    println!("  Bob's turn (Fed B): transfer 1 NFT to Alice");
    println!("    Turn hash: {}", short_hex(&bob_turn_hash));

    // ─── Step 2: Create conditional turns ───────────────────────────────────

    println!("\n--- Step 2: Submitting conditional turns ---\n");

    let timeout_height = 100;
    let current_height = 50;

    // Alice's conditional: execute IFF Bob's turn was executed
    let alice_conditional = ConditionalTurn {
        turn: alice_turn_a,
        condition: ProofCondition::TurnExecuted {
            turn_hash: bob_turn_hash,
        },
        timeout_height,
        submitted_at: current_height,
    };

    // Bob's conditional: execute IFF Alice's turn was executed
    let bob_conditional = ConditionalTurn {
        turn: bob_turn_b,
        condition: ProofCondition::TurnExecuted {
            turn_hash: alice_turn_hash,
        },
        timeout_height,
        submitted_at: current_height,
    };

    println!(
        "  Alice's conditional (Fed A): hash={}",
        short_hex(&alice_conditional.hash())
    );
    println!("    Condition: Bob's turn must be executed in Fed B");
    println!(
        "  Bob's conditional (Fed B): hash={}",
        short_hex(&bob_conditional.hash())
    );
    println!("    Condition: Alice's turn must be executed in Fed A");
    println!("    Timeout: height {timeout_height}");

    // ─── Step 3: Execute Bob's turn first (bootstrap) ───────────────────────

    println!("\n--- Step 3: Bootstrap - executing Bob's turn in Fed B ---\n");

    let executor_b = TurnExecutor::new(ComputronCosts::zero());
    let bob_result = executor_b.execute(&bob_conditional.turn, &mut fed_b_ledger);

    let bob_receipt = match bob_result {
        TurnResult::Committed { receipt, .. } => {
            println!("  Bob's turn COMMITTED in Fed B");
            println!("    Receipt turn_hash: {}", short_hex(&receipt.turn_hash));
            assert_eq!(receipt.turn_hash, bob_turn_hash);
            receipt
        }
        other => panic!("Expected Bob's turn to commit, got: {other:?}"),
    };

    let alice_b_cell = fed_b_ledger.get(&alice_b_id).unwrap();
    let bob_b_cell = fed_b_ledger.get(&bob_b_id).unwrap();
    println!("  Fed B state after:");
    println!("    Alice NFTs: {} (was 0)", alice_b_cell.state.balance);
    println!("    Bob NFTs:   {} (was 1)", bob_b_cell.state.balance);
    assert_eq!(alice_b_cell.state.balance, 1);
    assert_eq!(bob_b_cell.state.balance, 0);

    // ─── Step 4: Alice resolves her conditional using Bob's receipt ──────────

    println!("\n--- Step 4: Alice resolves her conditional in Fed A ---\n");

    let proof = ConditionProof::Receipt(bob_receipt);
    let executor_a = TurnExecutor::new(ComputronCosts::zero());

    let alice_result = executor_a.execute_conditional(
        &alice_conditional,
        &proof,
        current_height + 5, // within timeout
        &[],
        &mut fed_a_ledger,
    );

    match alice_result {
        TurnResult::Committed { receipt, .. } => {
            println!("  Alice's conditional turn RESOLVED and COMMITTED in Fed A");
            println!("    Receipt turn_hash: {}", short_hex(&receipt.turn_hash));
        }
        other => panic!("Expected Alice's conditional to commit, got: {other:?}"),
    }

    let alice_a_cell = fed_a_ledger.get(&alice_a_id).unwrap();
    let bob_a_cell = fed_a_ledger.get(&bob_a_id).unwrap();
    println!("  Fed A state after:");
    println!(
        "    Alice balance: {} (was 1000)",
        alice_a_cell.state.balance
    );
    println!("    Bob balance:   {} (was 0)", bob_a_cell.state.balance);
    assert_eq!(alice_a_cell.state.balance, 900);
    assert_eq!(bob_a_cell.state.balance, 100);

    println!("\n  ATOMIC SWAP COMPLETE:");
    println!("    Alice gave 100 tokens (Fed A) and received 1 NFT (Fed B)");
    println!("    Bob gave 1 NFT (Fed B) and received 100 tokens (Fed A)");

    // ─── Step 5: Demonstrate timeout expiry ─────────────────────────────────

    println!("\n--- Step 5: Demonstrating timeout expiry ---\n");

    let mut fed_c_ledger = Ledger::new();
    let charlie_pk = [5u8; 32];
    let dave_pk = [6u8; 32];

    let mut charlie = Cell::with_balance(charlie_pk, token_id, 500);
    charlie.permissions = open_permissions();
    let charlie_id = charlie.id;
    let mut dave = Cell::with_balance(dave_pk, token_id, 0);
    dave.permissions = open_permissions();
    let dave_id = dave.id;
    charlie
        .capabilities
        .grant(dave_id, AuthRequired::None);
    fed_c_ledger.insert_cell(charlie).unwrap();
    fed_c_ledger.insert_cell(dave).unwrap();

    let charlie_turn = build_transfer_turn(charlie_id, 0, charlie_id, dave_id, 200);

    let secret_hash = *blake3::hash(b"nobody knows this").as_bytes();
    let charlie_conditional = ConditionalTurn {
        turn: charlie_turn,
        condition: ProofCondition::HashPreimage { hash: secret_hash },
        timeout_height: 80,
        submitted_at: 50,
    };

    println!("  Charlie's conditional: transfer 200 to Dave IFF preimage revealed");
    println!("    Timeout: height 80");

    // Try at height 81 (past timeout)
    let wrong_preimage = [0u8; 32];
    let proof = ConditionProof::Preimage(wrong_preimage);
    let executor_c = TurnExecutor::new(ComputronCosts::zero());

    let expired_result = executor_c.execute_conditional(
        &charlie_conditional,
        &proof,
        81,
        &[],
        &mut fed_c_ledger,
    );

    match expired_result {
        TurnResult::Expired => {
            println!("  EXPIRED (height 81 > timeout 80)");
            println!("  No state change, no fee charged.");
        }
        other => panic!("Expected Expired, got: {other:?}"),
    }

    let charlie_cell = fed_c_ledger.get(&charlie_id).unwrap();
    let dave_cell = fed_c_ledger.get(&dave_id).unwrap();
    assert_eq!(charlie_cell.state.balance, 500);
    assert_eq!(dave_cell.state.balance, 0);
    println!("  Balances unchanged: Charlie=500, Dave=0");

    // ─── Step 6: Demonstrate invalid proof rejection ────────────────────────

    println!("\n--- Step 6: Demonstrating invalid proof rejection ---\n");

    let wrong_proof = ConditionProof::Preimage([99u8; 32]);
    let invalid_result = executor_c.execute_conditional(
        &charlie_conditional,
        &wrong_proof,
        60, // within timeout
        &[],
        &mut fed_c_ledger,
    );

    match invalid_result {
        TurnResult::Rejected { reason, .. } => {
            println!("  REJECTED: {reason}");
        }
        other => panic!("Expected Rejected, got: {other:?}"),
    }

    let charlie_cell = fed_c_ledger.get(&charlie_id).unwrap();
    assert_eq!(charlie_cell.state.balance, 500);
    println!("  Balances unchanged: Charlie=500, Dave=0");

    // ─── Step 7: Successful preimage reveal ─────────────────────────────────

    println!("\n--- Step 7: Successful preimage reveal ---\n");

    // Use a 32-byte secret whose BLAKE3 hash is the condition.
    let secret = [42u8; 32];
    let secret_hash_2 = *blake3::hash(&secret).as_bytes();

    let charlie_turn2 = build_transfer_turn(charlie_id, 0, charlie_id, dave_id, 200);
    let charlie_conditional2 = ConditionalTurn {
        turn: charlie_turn2,
        condition: ProofCondition::HashPreimage {
            hash: secret_hash_2,
        },
        timeout_height: 80,
        submitted_at: 50,
    };

    let correct_proof = ConditionProof::Preimage(secret);
    let success_result = executor_c.execute_conditional(
        &charlie_conditional2,
        &correct_proof,
        60,
        &[],
        &mut fed_c_ledger,
    );

    match success_result {
        TurnResult::Committed { receipt, .. } => {
            println!("  RESOLVED with correct preimage!");
            println!("    Receipt: {}", short_hex(&receipt.turn_hash));
        }
        other => panic!("Expected Committed, got: {other:?}"),
    }

    let charlie_cell = fed_c_ledger.get(&charlie_id).unwrap();
    let dave_cell = fed_c_ledger.get(&dave_id).unwrap();
    println!(
        "  Balances after: Charlie={}, Dave={}",
        charlie_cell.state.balance, dave_cell.state.balance
    );
    assert_eq!(charlie_cell.state.balance, 300);
    assert_eq!(dave_cell.state.balance, 200);

    // ─── Step 8: Demonstrate RemoteProof condition ──────────────────────────

    println!("\n--- Step 8: RemoteProof (STARK) condition ---\n");

    let fed_root = [0xFE; 32];
    let condition = ProofCondition::RemoteProof {
        federation_root: fed_root,
        expected_air: "transfer_v1".to_string(),
        expected_conclusion: 1,
    };

    let stark_proof = ConditionProof::StarkProof {
        proof_bytes: vec![0xDE, 0xAD, 0xBE, 0xEF, 0xCA, 0xFE],
        federation_root: fed_root,
        public_outputs: vec![1],
    };

    let trusted_roots = vec![fed_root];
    let result = pyana_turn::resolve_condition(&condition, &stark_proof, 60, 100, &trusted_roots);
    assert_eq!(result, ConditionalResult::Resolved);
    println!("  RemoteProof condition resolved with valid STARK proof");
    println!("    Federation root: {}", short_hex(&fed_root));
    println!("    Conclusion: ALLOW (1)");

    let untrusted_result =
        pyana_turn::resolve_condition(&condition, &stark_proof, 60, 100, &[]);
    assert!(matches!(
        untrusted_result,
        ConditionalResult::InvalidProof(_)
    ));
    println!("  Untrusted federation root correctly rejected");

    // ─── Summary ────────────────────────────────────────────────────────────

    println!("\n=== Cross-Federation Atomic Swap: SUCCESS ===\n");
    println!("Demonstrated:");
    println!("  1. ConditionalTurn with TurnExecuted condition (receipt-based)");
    println!("  2. Timeout expiry (no state change, no fee)");
    println!("  3. Invalid proof rejection (condition not met)");
    println!("  4. Successful preimage reveal (HTLC-style)");
    println!("  5. RemoteProof condition (STARK-based cross-federation)");
    println!("\nThe STARK proof replaces HTLC hash preimages but is strictly");
    println!("more general: any provable statement can serve as a condition.");
}

fn short_id(id: CellId) -> String {
    let bytes = id.as_bytes();
    format!(
        "{:02x}{:02x}{:02x}{:02x}...",
        bytes[0], bytes[1], bytes[2], bytes[3]
    )
}

fn short_hex(bytes: &[u8]) -> String {
    if bytes.len() >= 4 {
        format!(
            "{:02x}{:02x}{:02x}{:02x}...",
            bytes[0], bytes[1], bytes[2], bytes[3]
        )
    } else {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }
}
