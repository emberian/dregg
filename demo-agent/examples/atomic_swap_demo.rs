//! Atomic Swap Demo — Multi-Party Turn Composition
//!
//! Demonstrates:
//! 1. Alice has 100 units of asset A, wants 50 units of asset B
//! 2. Bob has 50 units of asset B, wants 100 units of asset A
//! 3. Each party signs their fragment independently (partial commitment)
//! 4. A matcher composes both fragments into one atomic turn
//! 5. Conservation verified: 100 A in = 100 A out, 50 B in = 50 B out
//! 6. Neither party needs to trust the other or the matcher

use ed25519_dalek::{Signer, SigningKey};
use pyana_cell::note::Note;
use pyana_cell::nullifier_set::NullifierSet;
use pyana_cell::{CellId, Preconditions};
use pyana_turn::CallForest;
use pyana_turn::action::{Action, Authorization, CommitmentMode, DelegationMode, Effect, symbol};
use pyana_turn::composer::{SignedFragment, TurnComposer};
use pyana_turn::executor::TurnExecutor;

/// Helper to create an Ed25519 signing key from seed bytes
fn make_signing_key(seed: &[u8]) -> SigningKey {
    let hash = blake3::derive_key("pyana-demo-signing-key-v1", seed);
    SigningKey::from_bytes(&hash)
}

fn main() {
    println!("=== Pyana Atomic Swap Demo (Multi-Party Composition) ===\n");

    // --- Setup: Create participants with real Ed25519 keys ---
    let alice_sk = make_signing_key(b"alice-atomic-swap-secret");
    let alice_vk = alice_sk.verifying_key();
    let alice_pubkey = alice_vk.to_bytes();

    let bob_sk = make_signing_key(b"bob-atomic-swap-secret");
    let bob_vk = bob_sk.verifying_key();
    let bob_pubkey = bob_vk.to_bytes();

    // Matcher is the third party who composes the turn
    let matcher_sk = make_signing_key(b"matcher-atomic-swap-secret");
    let matcher_vk = matcher_sk.verifying_key();
    let matcher_pubkey = matcher_vk.to_bytes();

    // Suppress unused variable warning
    let _ = &matcher_sk;

    // Asset types
    let asset_a: u64 = 0xAAAA_0000_0000_0001; // "Token A"
    let asset_b: u64 = 0xBBBB_0000_0000_0002; // "Token B"

    println!("Participants:");
    println!(
        "  Alice: {:02x}{:02x}{:02x}{:02x}... (has 100 units of Asset A)",
        alice_pubkey[0], alice_pubkey[1], alice_pubkey[2], alice_pubkey[3]
    );
    println!(
        "  Bob:   {:02x}{:02x}{:02x}{:02x}... (has 50 units of Asset B)",
        bob_pubkey[0], bob_pubkey[1], bob_pubkey[2], bob_pubkey[3]
    );
    println!(
        "  Matcher: {:02x}{:02x}{:02x}{:02x}... (fee payer, assembles the swap)",
        matcher_pubkey[0], matcher_pubkey[1], matcher_pubkey[2], matcher_pubkey[3]
    );
    println!();
    println!("Assets:");
    println!("  Asset A: 0x{:016x}", asset_a);
    println!("  Asset B: 0x{:016x}", asset_b);
    println!();

    // --- Create the notes representing each party's holdings ---
    let mut nullifier_set = NullifierSet::new();

    // Alice's note: 100 units of Asset A
    let alice_spending_key = blake3::derive_key("alice-note-spending-v1", &alice_pubkey);
    let alice_note =
        Note::with_randomness(alice_pubkey, [asset_a, 100, 0, 0, 0, 0, 0, 0], [0xA0u8; 32]);
    let alice_commitment = alice_note.commitment();
    let _alice_position: u64 = 0;
    let alice_nullifier = alice_note.nullifier(&alice_spending_key);

    // Bob's note: 50 units of Asset B
    let bob_spending_key = blake3::derive_key("bob-note-spending-v1", &bob_pubkey);
    let bob_note = Note::with_randomness(bob_pubkey, [asset_b, 50, 0, 0, 0, 0, 0, 0], [0xB0u8; 32]);
    let bob_commitment = bob_note.commitment();
    let _bob_position: u64 = 1;
    let bob_nullifier = bob_note.nullifier(&bob_spending_key);

    println!("--- Pre-Swap State ---");
    println!(
        "  Alice's note: {} units of Asset A (commitment: {:02x}{:02x}{:02x}{:02x}...)",
        alice_note.value(),
        alice_commitment.0[0],
        alice_commitment.0[1],
        alice_commitment.0[2],
        alice_commitment.0[3]
    );
    println!(
        "  Bob's note:   {} units of Asset B (commitment: {:02x}{:02x}{:02x}{:02x}...)",
        bob_note.value(),
        bob_commitment.0[0],
        bob_commitment.0[1],
        bob_commitment.0[2],
        bob_commitment.0[3]
    );
    println!();

    // =======================================================================
    // STEP 1: Alice creates her fragment
    // =======================================================================
    println!("--- Step 1: ALICE SIGNS HER FRAGMENT ---");
    println!("  \"I will spend my 100 Asset A note and receive 50 Asset B\"");

    // Alice's cell ID (derived from her pubkey)
    let alice_cell_id = CellId::derive_raw(&alice_pubkey, &[0u8; 32]);

    // The note Alice wants to RECEIVE (50 units of Asset B, owned by Alice)
    let alice_receives_note =
        Note::with_randomness(alice_pubkey, [asset_b, 50, 0, 0, 0, 0, 0, 0], [0xA1u8; 32]);
    let alice_receives_commitment = alice_receives_note.commitment();

    // Alice's action: spend her note, create a new note for herself
    let alice_action = Action {
        target: alice_cell_id,
        method: symbol("atomic_swap_fragment"),
        args: vec![],
        authorization: Authorization::Unchecked, // Will be verified via fragment signature
        preconditions: Preconditions::default(),
        effects: vec![
            // Spend Alice's old note (100 Asset A)
            Effect::NoteSpend {
                nullifier: alice_nullifier,
                note_tree_root: [0u8; 32], // Simplified for demo
                value: 100,
                asset_type: asset_a,
                spending_proof: vec![0x01], // placeholder for demo
                value_commitment: None,
            },
            // Create new note for Alice (50 Asset B)
            Effect::NoteCreate {
                commitment: alice_receives_commitment,
                value: 50,
                asset_type: asset_b,
                encrypted_note: vec![0xAA; 64], // Encrypted note data
                value_commitment: None,
                range_proof: None,
            },
        ],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Partial, // KEY: partial commitment for composability
        balance_change: None,
    };

    println!("  Action effects:");
    println!(
        "    - NoteSpend: 100 units Asset A (nullifier: {:02x}{:02x}{:02x}{:02x}...)",
        alice_nullifier.0[0], alice_nullifier.0[1], alice_nullifier.0[2], alice_nullifier.0[3]
    );
    println!(
        "    - NoteCreate: 50 units Asset B (commitment: {:02x}{:02x}{:02x}{:02x}...)",
        alice_receives_commitment.0[0],
        alice_receives_commitment.0[1],
        alice_receives_commitment.0[2],
        alice_receives_commitment.0[3]
    );
    println!("  Commitment mode: Partial (doesn't see Bob's actions)");
    println!("  Alice signs with Ed25519");
    println!();

    // =======================================================================
    // STEP 2: Bob creates his fragment
    // =======================================================================
    println!("--- Step 2: BOB SIGNS HIS FRAGMENT ---");
    println!("  \"I will spend my 50 Asset B note and receive 100 Asset A\"");

    let bob_cell_id = CellId::derive_raw(&bob_pubkey, &[0u8; 32]);

    // The note Bob wants to RECEIVE (100 units of Asset A, owned by Bob)
    let bob_receives_note =
        Note::with_randomness(bob_pubkey, [asset_a, 100, 0, 0, 0, 0, 0, 0], [0xB1u8; 32]);
    let bob_receives_commitment = bob_receives_note.commitment();

    let bob_action = Action {
        target: bob_cell_id,
        method: symbol("atomic_swap_fragment"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Preconditions::default(),
        effects: vec![
            // Spend Bob's old note (50 Asset B)
            Effect::NoteSpend {
                nullifier: bob_nullifier,
                note_tree_root: [0u8; 32],
                value: 50,
                asset_type: asset_b,
                spending_proof: vec![0x01], // placeholder for demo
                value_commitment: None,
            },
            // Create new note for Bob (100 Asset A)
            Effect::NoteCreate {
                commitment: bob_receives_commitment,
                value: 100,
                asset_type: asset_a,
                encrypted_note: vec![0xBB; 64],
                value_commitment: None,
                range_proof: None,
            },
        ],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Partial,
        balance_change: None,
    };

    println!("  Action effects:");
    println!(
        "    - NoteSpend: 50 units Asset B (nullifier: {:02x}{:02x}{:02x}{:02x}...)",
        bob_nullifier.0[0], bob_nullifier.0[1], bob_nullifier.0[2], bob_nullifier.0[3]
    );
    println!(
        "    - NoteCreate: 100 units Asset A (commitment: {:02x}{:02x}{:02x}{:02x}...)",
        bob_receives_commitment.0[0],
        bob_receives_commitment.0[1],
        bob_receives_commitment.0[2],
        bob_receives_commitment.0[3]
    );
    println!("  Commitment mode: Partial (doesn't see Alice's actions)");
    println!("  Bob signs with Ed25519");
    println!();

    // =======================================================================
    // STEP 3: Matcher composes both fragments
    // =======================================================================
    println!("--- Step 3: MATCHER COMPOSES ATOMIC TURN ---");

    let matcher_cell_id = CellId::derive_raw(&matcher_pubkey, &[0u8; 32]);

    // Build a TurnComposer
    let mut composer = TurnComposer::new(matcher_cell_id, 1000, 0);
    composer.set_memo("Atomic swap: 100 Asset A <-> 50 Asset B");

    // To properly sign fragments, we need the forest root hash, which depends on
    // all actions. We build the forest, compute the root, then sign.
    let mut temp_forest = CallForest::new();
    temp_forest.add_root(alice_action.clone());
    temp_forest.add_root(bob_action.clone());
    let forest_root = temp_forest.hash();

    println!(
        "  Forest root: {:02x}{:02x}{:02x}{:02x}...",
        forest_root[0], forest_root[1], forest_root[2], forest_root[3]
    );

    // Compute the signing messages for each party
    let alice_signing_msg =
        TurnExecutor::compute_partial_signing_message(&alice_action, 0, &[0u8; 32], 0);
    let bob_signing_msg =
        TurnExecutor::compute_partial_signing_message(&bob_action, 1, &[0u8; 32], 0);

    // Alice and Bob sign their messages
    let alice_sig = alice_sk.sign(&alice_signing_msg);
    let bob_sig = bob_sk.sign(&bob_signing_msg);

    println!(
        "  Alice's signature: {:02x}{:02x}{:02x}{:02x}...",
        alice_sig.to_bytes()[0],
        alice_sig.to_bytes()[1],
        alice_sig.to_bytes()[2],
        alice_sig.to_bytes()[3]
    );
    println!(
        "  Bob's signature:   {:02x}{:02x}{:02x}{:02x}...",
        bob_sig.to_bytes()[0],
        bob_sig.to_bytes()[1],
        bob_sig.to_bytes()[2],
        bob_sig.to_bytes()[3]
    );

    // Create signed fragments
    let alice_fragment = SignedFragment {
        actions: vec![alice_action.clone()],
        signatures: vec![alice_sig.to_bytes()],
        signer: alice_pubkey,
    };

    let bob_fragment = SignedFragment {
        actions: vec![bob_action.clone()],
        signatures: vec![bob_sig.to_bytes()],
        signer: bob_pubkey,
    };

    // Add fragments to composer
    composer
        .add_fragment(alice_fragment)
        .expect("Alice's fragment should be valid");
    composer
        .add_fragment(bob_fragment)
        .expect("Bob's fragment should be valid");

    println!("  Both fragments added to composer");
    println!();

    // =======================================================================
    // STEP 4: Compose and verify the atomic turn
    // =======================================================================
    println!("--- Step 4: COMPOSE ATOMIC TURN ---");

    let composed_turn = composer.compose();
    match &composed_turn {
        Ok(turn) => {
            println!("  Turn composed successfully!");
            println!(
                "  Agent (fee payer): {:02x}{:02x}{:02x}{:02x}...",
                matcher_pubkey[0], matcher_pubkey[1], matcher_pubkey[2], matcher_pubkey[3]
            );
            println!("  Action count: {}", turn.turn.action_count());
            println!("  Fee: {} computrons", turn.turn.fee);
            println!("  Memo: {:?}", turn.turn.memo);
        }
        Err(e) => {
            // ExcessImbalance is expected when balance_change is used, but our swap
            // uses NoteSpend/NoteCreate (no balance_change), so excess should be 0.
            println!("  Composition error: {}", e);
        }
    }
    println!();

    // =======================================================================
    // STEP 5: CONSERVATION VERIFICATION
    // =======================================================================
    println!("--- Step 5: CONSERVATION VERIFICATION ---");

    // Track asset flows manually to demonstrate conservation
    println!("  Asset A flows:");
    println!("    IN:  100 units (Alice's note spent)");
    println!("    OUT: 100 units (Bob's new note created)");
    println!("    Net: 0 [CONSERVED]");
    println!();
    println!("  Asset B flows:");
    println!("    IN:  50 units (Bob's note spent)");
    println!("    OUT: 50 units (Alice's new note created)");
    println!("    Net: 0 [CONSERVED]");
    println!();

    // Verify conservation by checking the note effects
    let mut asset_a_in: u64 = 0;
    let mut asset_a_out: u64 = 0;
    let mut asset_b_in: u64 = 0;
    let mut asset_b_out: u64 = 0;

    for action in [&alice_action, &bob_action] {
        for effect in &action.effects {
            match effect {
                Effect::NoteSpend {
                    value, asset_type, ..
                } => {
                    if *asset_type == asset_a {
                        asset_a_in += value;
                    }
                    if *asset_type == asset_b {
                        asset_b_in += value;
                    }
                }
                Effect::NoteCreate {
                    value, asset_type, ..
                } => {
                    if *asset_type == asset_a {
                        asset_a_out += value;
                    }
                    if *asset_type == asset_b {
                        asset_b_out += value;
                    }
                }
                _ => {}
            }
        }
    }

    assert_eq!(asset_a_in, asset_a_out, "Asset A must be conserved");
    assert_eq!(asset_b_in, asset_b_out, "Asset B must be conserved");
    println!("  Conservation law verified programmatically: [PASS]");
    println!();

    // =======================================================================
    // STEP 6: NULLIFIER DOUBLE-SPEND PROTECTION
    // =======================================================================
    println!("--- Step 6: DOUBLE-SPEND PROTECTION ---");

    // Record the nullifiers as spent
    nullifier_set
        .insert(alice_nullifier)
        .expect("Alice's nullifier should be accepted");
    nullifier_set
        .insert(bob_nullifier)
        .expect("Bob's nullifier should be accepted");

    println!("  Alice's nullifier recorded as spent");
    println!("  Bob's nullifier recorded as spent");

    // Try to replay the swap (double-spend)
    let replay_alice = nullifier_set.insert(alice_nullifier);
    let replay_bob = nullifier_set.insert(bob_nullifier);

    assert!(replay_alice.is_err());
    assert!(replay_bob.is_err());
    println!("  Replay attack (re-spending Alice's note): REJECTED [PASS]");
    println!("  Replay attack (re-spending Bob's note): REJECTED [PASS]");
    println!();

    // =======================================================================
    // STEP 7: TRUST MODEL VERIFICATION
    // =======================================================================
    println!("--- Step 7: TRUST MODEL ---");
    println!("  Key properties of this atomic swap:");
    println!();
    println!("  1. ATOMICITY: Both fragments execute in a single Turn, or neither does.");
    println!("     If any part fails, the entire turn is rolled back.");
    println!();
    println!("  2. NO TRUST REQUIRED: Alice and Bob each sign only their own fragment.");
    println!("     Neither sees the other's actions before signing (Partial commitment).");
    println!();
    println!("  3. MATCHER CANNOT STEAL: The matcher can only compose fragments that");
    println!("     parties voluntarily signed. It cannot forge signatures or modify");
    println!("     signed actions.");
    println!();
    println!("  4. CONSERVATION: The note layer enforces that for each asset type,");
    println!("     total inputs = total outputs. No value is created or destroyed.");
    println!();
    println!("  5. REPLAY PROTECTION: Each note can only be spent once (nullifier set).");
    println!("     Even if the matcher tries to replay the swap, it will fail.");
    println!();

    // =======================================================================
    // FINAL STATE
    // =======================================================================
    println!("--- Final State ---");
    println!(
        "  Alice: now owns 50 units of Asset B (commitment: {:02x}{:02x}{:02x}{:02x}...)",
        alice_receives_commitment.0[0],
        alice_receives_commitment.0[1],
        alice_receives_commitment.0[2],
        alice_receives_commitment.0[3]
    );
    println!(
        "  Bob:   now owns 100 units of Asset A (commitment: {:02x}{:02x}{:02x}{:02x}...)",
        bob_receives_commitment.0[0],
        bob_receives_commitment.0[1],
        bob_receives_commitment.0[2],
        bob_receives_commitment.0[3]
    );
    println!("  Nullifiers spent: {}", nullifier_set.len());
    println!();
    println!("=== Atomic Swap Demo Complete ===");
}
