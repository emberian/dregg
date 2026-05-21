//! ProofObligation: Bonded Cross-Federation Atomic Swap
//!
//! Demonstrates the categorical dual of ConditionalTurn:
//! - ConditionalTurn: "I'll execute when you prove X"
//! - ProofObligation: "I commit to proving X, and I've locked stake against failure"
//!
//! This eliminates the "free option" problem: without bonding, a party can create
//! conditional turns and never deliver, wasting the counterparty's time/resources.
//!
//! ## Happy Path
//! 1. Alice creates ProofObligation (bonded to prove her transfer to Bob)
//! 2. Bob creates ProofObligation (bonded to prove his transfer to Alice)
//! 3. Both deliver proofs before deadline -> stakes returned
//!
//! ## Adversarial Path
//! 4. Bob fails to deliver proof -> Alice slashes Bob's stake as compensation

use pyana_cell::note::NoteCommitment;
use pyana_cell::CellId;
use pyana_turn::{
    ConditionProof, ProofCondition, ProofObligation,
    obligation::{ObligationOutcome, check_expiry, create_obligation, fulfill_obligation},
};

fn short_id(id: CellId) -> String {
    format!("{:02x}{:02x}{:02x}{:02x}", id.0[0], id.0[1], id.0[2], id.0[3])
}

fn short_hex(bytes: &[u8; 32]) -> String {
    format!("{:02x}{:02x}{:02x}{:02x}...", bytes[0], bytes[1], bytes[2], bytes[3])
}

fn main() {
    println!("=== ProofObligation: Bonded Cross-Federation Atomic Swap ===\n");

    // ─── Setup ──────────────────────────────────────────────────────────────────

    let alice = CellId([1u8; 32]);
    let bob = CellId([2u8; 32]);
    let deadline_height = 100u64;

    // Stakes: each party locks a note commitment as bond.
    let alice_stake = NoteCommitment([0xA1; 32]);
    let bob_stake = NoteCommitment([0xB2; 32]);

    // Federation roots (trusted by both parties).
    let fed_a_root = [0xFA; 32];
    let fed_b_root = [0xFB; 32];
    let trusted_roots = [fed_a_root, fed_b_root];

    println!("Participants:");
    println!("  Alice: {} (obligor in Fed A)", short_id(alice));
    println!("  Bob:   {} (obligor in Fed B)", short_id(bob));
    println!("  Deadline: height {}", deadline_height);
    println!("  Alice stake: {}", short_hex(&alice_stake.0));
    println!("  Bob stake:   {}", short_hex(&bob_stake.0));

    // ─── Step 1: Create Proof Obligations ───────────────────────────────────────

    println!("\n--- Step 1: Creating bonded proof obligations ---\n");

    // Alice obligates herself to prove she transferred tokens to Bob in Fed A.
    let alice_condition = ProofCondition::RemoteProof {
        federation_root: fed_a_root,
        expected_air: "transfer_air".to_string(),
        expected_conclusion: 1, // ALLOW = transfer happened
    };

    let alice_obligation = create_obligation(
        alice,
        bob, // Bob benefits if Alice fails
        alice_condition,
        deadline_height,
        alice_stake,
    );

    // Bob obligates himself to prove he transferred NFT to Alice in Fed B.
    let bob_condition = ProofCondition::RemoteProof {
        federation_root: fed_b_root,
        expected_air: "nft_transfer_air".to_string(),
        expected_conclusion: 1,
    };

    let bob_obligation = create_obligation(
        bob,
        alice, // Alice benefits if Bob fails
        bob_condition,
        deadline_height,
        bob_stake,
    );

    println!("  Alice's obligation: {}", short_hex(&alice_obligation.id));
    println!("    Prove: transfer tokens to Bob in Fed A");
    println!("    Stake locked: {} (forfeit if she fails)", short_hex(&alice_stake.0));
    println!("  Bob's obligation: {}", short_hex(&bob_obligation.id));
    println!("    Prove: transfer NFT to Alice in Fed B");
    println!("    Stake locked: {} (forfeit if he fails)", short_hex(&bob_stake.0));

    // ─── Step 2: Happy Path — Both Deliver Proofs ───────────────────────────────

    println!("\n--- Step 2: Happy Path — Both deliver proofs ---\n");

    let current_height = 60; // Before deadline

    // Alice delivers her proof (STARK proof of transfer in Fed A).
    let alice_proof = ConditionProof::StarkProof {
        proof_bytes: vec![0xDE, 0xAD, 0xBE, 0xEF, 0xCA, 0xFE],
        federation_root: fed_a_root,
        public_outputs: vec![1], // conclusion = ALLOW
    };

    let alice_result = fulfill_obligation(
        &alice_obligation,
        &alice_proof,
        current_height,
        &trusted_roots,
    );

    match &alice_result {
        Ok(ObligationOutcome::Fulfilled { .. }) => {
            println!("  Alice fulfilled obligation at height {}!", current_height);
            println!("    -> Stake {} returned to Alice", short_hex(&alice_stake.0));
        }
        Ok(other) => println!("  Unexpected outcome: {:?}", other),
        Err(e) => println!("  ERROR: {}", e),
    }
    assert!(alice_result.is_ok());

    // Bob delivers his proof (STARK proof of NFT transfer in Fed B).
    let bob_proof = ConditionProof::StarkProof {
        proof_bytes: vec![0xBA, 0xDC, 0x0F, 0xFE, 0xE0],
        federation_root: fed_b_root,
        public_outputs: vec![1],
    };

    let bob_result = fulfill_obligation(
        &bob_obligation,
        &bob_proof,
        current_height,
        &trusted_roots,
    );

    match &bob_result {
        Ok(ObligationOutcome::Fulfilled { .. }) => {
            println!("  Bob fulfilled obligation at height {}!", current_height);
            println!("    -> Stake {} returned to Bob", short_hex(&bob_stake.0));
        }
        Ok(other) => println!("  Unexpected outcome: {:?}", other),
        Err(e) => println!("  ERROR: {}", e),
    }
    assert!(bob_result.is_ok());

    println!("\n  Result: Both parties fulfilled. Both stakes returned.");
    println!("  The conditional turns (not shown) now resolve and execute atomically.");

    // ─── Step 3: Adversarial Path — Bob Fails to Deliver ────────────────────────

    println!("\n--- Step 3: Adversarial Path — Bob fails to deliver ---\n");

    // Create fresh obligations for the adversarial scenario.
    let bob_condition_2 = ProofCondition::RemoteProof {
        federation_root: fed_b_root,
        expected_air: "nft_transfer_air".to_string(),
        expected_conclusion: 1,
    };

    let bob_obligation_2 = create_obligation(
        bob,
        alice,
        bob_condition_2,
        deadline_height,
        bob_stake,
    );

    println!("  Bob's obligation: {}", short_hex(&bob_obligation_2.id));
    println!("  Simulating: Bob does NOT deliver proof...");
    println!("  Time passes... height advances past deadline.");

    // Height passes deadline.
    let expired_height = 101;

    // Check expiry.
    let expiry = check_expiry(&bob_obligation_2, expired_height);
    match &expiry {
        Some(ObligationOutcome::Slashed) => {
            println!("\n  Obligation EXPIRED at height {}!", expired_height);
            println!("  -> Bob's stake {} SLASHED to Alice", short_hex(&bob_stake.0));
            println!("  -> Alice receives compensation for wasted time/resources");
        }
        Some(other) => println!("  Unexpected: {:?}", other),
        None => println!("  ERROR: obligation should have expired"),
    }
    assert!(matches!(expiry, Some(ObligationOutcome::Slashed)));

    // Verify Bob cannot fulfill after deadline.
    println!("\n  Bob tries to fulfill after deadline...");
    let late_proof = ConditionProof::StarkProof {
        proof_bytes: vec![0xBA, 0xDC, 0x0F, 0xFE, 0xE0],
        federation_root: fed_b_root,
        public_outputs: vec![1],
    };
    let late_result = fulfill_obligation(
        &bob_obligation_2,
        &late_proof,
        expired_height,
        &trusted_roots,
    );
    match &late_result {
        Err(e) => {
            println!("  REJECTED: {}", e);
        }
        Ok(_) => println!("  ERROR: should have been rejected"),
    }
    assert!(late_result.is_err());

    // ─── Step 4: Attempt to Slash Before Deadline ───────────────────────────────

    println!("\n--- Step 4: Cannot slash before deadline ---\n");

    let bob_condition_3 = ProofCondition::HashPreimage { hash: [0xCC; 32] };
    let bob_obligation_3 = create_obligation(bob, alice, bob_condition_3, 100, bob_stake);

    let early_slash = check_expiry(&bob_obligation_3, 50);
    match early_slash {
        None => {
            println!("  check_expiry at height 50 (deadline=100): None");
            println!("  -> Cannot slash before deadline. Obligation still pending.");
        }
        Some(_) => println!("  ERROR: should not be slashable before deadline"),
    }
    assert!(early_slash.is_none());

    // ─── Summary ────────────────────────────────────────────────────────────────

    println!("\n=== Summary ===\n");
    println!("ProofObligation is the categorical dual of ConditionalTurn:");
    println!("  ConditionalTurn: 'I'll act when you prove X'");
    println!("  ProofObligation: 'I commit to proving X, with bonded stake'");
    println!();
    println!("Together they form a compact closure:");
    println!("  1. Both parties create obligations (bond stake)");
    println!("  2. Both parties create conditional turns (conditioned on each other)");
    println!("  3. Success: both prove -> both execute, stakes returned");
    println!("  4. Failure: defaulter's stake slashed to victim (compensation)");
    println!();
    println!("This eliminates the 'free option' problem in cross-federation atomicity.");
}
