//! NFT Lifecycle Demo
//!
//! Demonstrates:
//! 1. Mint: Create a note with unique asset_id, value=0 (non-fungible)
//! 2. Transfer: Spend the old note (reveal nullifier), create new note (same asset_id, new owner)
//! 3. Verify: The new note preserves identity (same fields[0]) with different owner
//! 4. Double-spend prevention: Attempting to spend the original note again is rejected
//! 5. Provenance: The chain of nullifiers traces ownership history

use pyana_cell::note::Note;
use pyana_cell::nullifier_set::NullifierSet;

fn main() {
    println!("=== Pyana NFT Lifecycle Demo ===\n");

    // --- Setup: Create two owners with Ed25519-style keys ---
    let alice_spending_key = blake3::derive_key("alice-spending-key-v1", b"alice-secret");
    let alice_pubkey = blake3::derive_key("alice-pubkey-v1", &alice_spending_key);

    let bob_spending_key = blake3::derive_key("bob-spending-key-v1", b"bob-secret");
    let bob_pubkey = blake3::derive_key("bob-pubkey-v1", &bob_spending_key);

    let carol_spending_key = blake3::derive_key("carol-spending-key-v1", b"carol-secret");
    let carol_pubkey = blake3::derive_key("carol-pubkey-v1", &carol_spending_key);

    // The unique asset identifier for our NFT (hash of the artwork metadata)
    let asset_id = u64::from_le_bytes(
        blake3::hash(b"artwork-001: Sunset over the Pyana Valley").as_bytes()[..8]
            .try_into()
            .unwrap(),
    );

    println!("Participants:");
    println!("  Alice (minter): {:02x}{:02x}{:02x}{:02x}...", alice_pubkey[0], alice_pubkey[1], alice_pubkey[2], alice_pubkey[3]);
    println!("  Bob:            {:02x}{:02x}{:02x}{:02x}...", bob_pubkey[0], bob_pubkey[1], bob_pubkey[2], bob_pubkey[3]);
    println!("  Carol:          {:02x}{:02x}{:02x}{:02x}...", carol_pubkey[0], carol_pubkey[1], carol_pubkey[2], carol_pubkey[3]);
    println!("  NFT asset_id:   0x{:016x}", asset_id);
    println!();

    // Global nullifier set (tracks all spent notes)
    let mut nullifier_set = NullifierSet::new();

    // =======================================================================
    // STEP 1: MINT — Alice creates the NFT note
    // =======================================================================
    println!("--- Step 1: MINT (Alice creates NFT) ---");

    // NFT note: fields[0] = unique asset ID, fields[1] = 0 (not fungible)
    // fields[2] = edition number, fields[3] = mint timestamp
    let mint_fields = [asset_id, 0, 1, 1700000000, 0, 0, 0, 0];
    let nft_note_alice = Note::with_randomness(alice_pubkey, mint_fields, [0x42u8; 32]);
    let alice_commitment = nft_note_alice.commitment();
    let alice_position: u64 = 0; // First note in the tree

    println!("  Created note with commitment: {:02x}{:02x}{:02x}{:02x}...",
        alice_commitment.0[0], alice_commitment.0[1], alice_commitment.0[2], alice_commitment.0[3]);
    println!("  Owner: Alice");
    println!("  Asset ID: 0x{:016x}", nft_note_alice.fields[0]);
    println!("  Edition: #{}", nft_note_alice.fields[2]);
    println!("  Is fungible: {} (correct for NFT)", nft_note_alice.is_fungible());
    println!();

    // =======================================================================
    // STEP 2: TRANSFER — Alice transfers NFT to Bob
    // =======================================================================
    println!("--- Step 2: TRANSFER (Alice -> Bob) ---");

    // Alice computes and reveals her nullifier (proves she owns the note)
    let nullifier_alice = nft_note_alice.nullifier(&alice_spending_key, alice_position);
    println!("  Alice reveals nullifier: {:02x}{:02x}{:02x}{:02x}...",
        nullifier_alice.0[0], nullifier_alice.0[1], nullifier_alice.0[2], nullifier_alice.0[3]);

    // Insert nullifier into the set (spend the note)
    nullifier_set.insert(nullifier_alice).expect("First spend should succeed");
    println!("  Nullifier accepted (note is now spent)");

    // Create new note with same asset_id but Bob as owner
    let transfer_fields = [asset_id, 0, 1, 1700000000, 0, 0, 0, 0];
    let nft_note_bob = Note::with_randomness(bob_pubkey, transfer_fields, [0x43u8; 32]);
    let bob_commitment = nft_note_bob.commitment();
    let bob_position: u64 = 1; // Second note in the tree

    println!("  Created new note for Bob: {:02x}{:02x}{:02x}{:02x}...",
        bob_commitment.0[0], bob_commitment.0[1], bob_commitment.0[2], bob_commitment.0[3]);
    println!();

    // =======================================================================
    // STEP 3: VERIFY — Asset identity preserved, owner changed
    // =======================================================================
    println!("--- Step 3: VERIFY (identity preserved) ---");

    assert_eq!(nft_note_alice.fields[0], nft_note_bob.fields[0],
        "Asset ID must be preserved across transfers");
    assert_eq!(nft_note_alice.fields[0], asset_id);
    assert_ne!(nft_note_alice.owner, nft_note_bob.owner,
        "Owner must change on transfer");
    assert_ne!(alice_commitment, bob_commitment,
        "Commitments must differ (different owner + randomness)");

    println!("  Asset ID preserved: 0x{:016x} == 0x{:016x} [PASS]",
        nft_note_alice.fields[0], nft_note_bob.fields[0]);
    println!("  Owner changed: Alice -> Bob [PASS]");
    println!("  Commitments differ: [PASS]");
    println!("  Original note is spent (nullifier in set): {} [PASS]",
        nullifier_set.contains(&nullifier_alice));
    println!();

    // =======================================================================
    // STEP 4: DOUBLE-SPEND PREVENTION
    // =======================================================================
    println!("--- Step 4: DOUBLE-SPEND PREVENTION ---");

    // An adversary (or Alice herself) tries to spend the same note again
    println!("  Adversary attempts to re-spend Alice's original note...");
    let double_spend_result = nullifier_set.insert(nullifier_alice);

    match double_spend_result {
        Err(pyana_cell::note::NoteError::DoubleSpend { nullifier }) => {
            println!("  REJECTED: double-spend detected!");
            println!("  Nullifier {:02x}{:02x}{:02x}{:02x}... already in set",
                nullifier.0[0], nullifier.0[1], nullifier.0[2], nullifier.0[3]);
        }
        _ => panic!("Should have been rejected as double-spend!"),
    }

    // Also demonstrate non-membership proof for Bob's note (proving it's NOT spent)
    let nullifier_bob = nft_note_bob.nullifier(&bob_spending_key, bob_position);
    let non_membership = nullifier_set.prove_non_membership(&nullifier_bob);
    assert!(non_membership.is_some(), "Should be able to prove Bob's note is NOT spent");
    let proof = non_membership.unwrap();
    let root = nullifier_set.root();
    assert!(NullifierSet::verify_non_membership(&proof, &root));
    println!("  Bob's note is provably unspent (non-membership proof valid) [PASS]");
    println!();

    // =======================================================================
    // STEP 5: PROVENANCE — Chain of ownership via nullifiers
    // =======================================================================
    println!("--- Step 5: PROVENANCE (ownership chain) ---");

    // Bob transfers to Carol
    let nullifier_bob_spend = nft_note_bob.nullifier(&bob_spending_key, bob_position);
    nullifier_set.insert(nullifier_bob_spend).expect("Bob's spend should succeed");

    let nft_note_carol = Note::with_randomness(carol_pubkey, transfer_fields, [0x44u8; 32]);
    let carol_commitment = nft_note_carol.commitment();
    let _carol_position: u64 = 2;

    println!("  Bob transfers NFT to Carol");
    println!("  Bob reveals nullifier: {:02x}{:02x}{:02x}{:02x}...",
        nullifier_bob_spend.0[0], nullifier_bob_spend.0[1], nullifier_bob_spend.0[2], nullifier_bob_spend.0[3]);
    println!("  New note for Carol: {:02x}{:02x}{:02x}{:02x}...",
        carol_commitment.0[0], carol_commitment.0[1], carol_commitment.0[2], carol_commitment.0[3]);
    println!();

    // The provenance chain:
    println!("  PROVENANCE CHAIN (nullifier history):");
    println!("  ┌─────────────────────────────────────────────────────┐");
    println!("  │ Mint (Alice)                                        │");
    println!("  │   commitment: {:02x}{:02x}{:02x}{:02x}...                      │",
        alice_commitment.0[0], alice_commitment.0[1], alice_commitment.0[2], alice_commitment.0[3]);
    println!("  │           |                                         │");
    println!("  │   nullifier: {:02x}{:02x}{:02x}{:02x}... (spent by Alice)      │",
        nullifier_alice.0[0], nullifier_alice.0[1], nullifier_alice.0[2], nullifier_alice.0[3]);
    println!("  │           v                                         │");
    println!("  │ Transfer -> Bob                                     │");
    println!("  │   commitment: {:02x}{:02x}{:02x}{:02x}...                      │",
        bob_commitment.0[0], bob_commitment.0[1], bob_commitment.0[2], bob_commitment.0[3]);
    println!("  │           |                                         │");
    println!("  │   nullifier: {:02x}{:02x}{:02x}{:02x}... (spent by Bob)        │",
        nullifier_bob_spend.0[0], nullifier_bob_spend.0[1], nullifier_bob_spend.0[2], nullifier_bob_spend.0[3]);
    println!("  │           v                                         │");
    println!("  │ Transfer -> Carol                                   │");
    println!("  │   commitment: {:02x}{:02x}{:02x}{:02x}...                      │",
        carol_commitment.0[0], carol_commitment.0[1], carol_commitment.0[2], carol_commitment.0[3]);
    println!("  │   (current owner, unspent)                          │");
    println!("  └─────────────────────────────────────────────────────┘");
    println!();

    // Final state
    println!("  Nullifier set size: {} (2 transfers completed)", nullifier_set.len());
    println!("  Asset identity preserved through all transfers: 0x{:016x}", asset_id);
    assert_eq!(nft_note_carol.fields[0], asset_id);
    println!();
    println!("=== NFT Demo Complete ===");
}
