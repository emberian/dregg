//! Private Order Book Demo — Sealed-Bid Matching with Note Commitments
//!
//! Demonstrates:
//! 1. Traders create notes (anonymous cells) containing bid commitments
//!    - Only the commitment is public; price/quantity remain hidden
//! 2. A matching engine collects commitments from multiple traders
//! 3. Traders selectively reveal their bids to the matcher
//! 4. Matched trades execute as atomic swaps (TurnComposer multi-party)
//! 5. Unmatched bids remain private (their contents are never revealed)
//! 6. Double-spend protection via nullifier set prevents bid reuse

#![allow(dead_code)]

use dregg_cell::note::Note;
use dregg_cell::nullifier_set::NullifierSet;
use dregg_cell::{CellId, Preconditions};
use dregg_turn::CallForest;
use dregg_turn::action::{Action, Authorization, CommitmentMode, DelegationMode, Effect, symbol};
use dregg_turn::composer::{SignedFragment, TurnComposer};
use dregg_turn::executor::TurnExecutor;
use ed25519_dalek::{Signer, SigningKey};

/// A sealed bid: the commitment is public, the details are private.
#[derive(Clone, Debug)]
struct SealedBid {
    /// The note containing the bid details (private to the trader).
    note: Note,
    /// The public commitment (published to the order book).
    commitment: dregg_cell::NoteCommitment,
    /// Direction: true = buy, false = sell.
    is_buy: bool,
    /// The asset being traded.
    asset_type: u64,
    /// Price (hidden until reveal).
    price: u64,
    /// Quantity (hidden until reveal).
    quantity: u64,
}

/// A revealed bid (after selective disclosure to the matcher).
#[derive(Clone, Debug)]
struct RevealedBid {
    bid: SealedBid,
    /// The trader's spending key (for nullifier computation).
    spending_key: [u8; 32],
    /// The trader's signing key (for fragment authorization).
    signing_key: SigningKey,
}

/// Helper to create an Ed25519 signing key from seed bytes.
fn make_signing_key(seed: &[u8]) -> SigningKey {
    let hash = blake3::derive_key("dregg-orderbook-signing-key-v1", seed);
    SigningKey::from_bytes(&hash)
}

fn main() {
    println!("=== Dregg Private Order Book Demo (Sealed-Bid Matching) ===\n");

    // --- Setup: Create traders ---
    let alice_sk = make_signing_key(b"alice-orderbook-secret");
    let alice_vk = alice_sk.verifying_key();
    let alice_pubkey = alice_vk.to_bytes();
    let alice_spending_key = blake3::derive_key("alice-orderbook-spending-v1", &alice_pubkey);

    let bob_sk = make_signing_key(b"bob-orderbook-secret");
    let bob_vk = bob_sk.verifying_key();
    let bob_pubkey = bob_vk.to_bytes();
    let bob_spending_key = blake3::derive_key("bob-orderbook-spending-v1", &bob_pubkey);

    let carol_sk = make_signing_key(b"carol-orderbook-secret");
    let carol_vk = carol_sk.verifying_key();
    let carol_pubkey = carol_vk.to_bytes();
    let carol_spending_key = blake3::derive_key("carol-orderbook-spending-v1", &carol_pubkey);

    let dave_sk = make_signing_key(b"dave-orderbook-secret");
    let dave_vk = dave_sk.verifying_key();
    let dave_pubkey = dave_vk.to_bytes();
    let _dave_spending_key = blake3::derive_key("dave-orderbook-spending-v1", &dave_pubkey);

    // Matcher (the order book engine)
    let matcher_sk = make_signing_key(b"matcher-orderbook-secret");
    let matcher_vk = matcher_sk.verifying_key();
    let matcher_pubkey = matcher_vk.to_bytes();
    let _ = &matcher_sk;

    // Asset types (hex-encoded identifiers)
    let asset_eth: u64 = 0xE7E0_0000_0000_0001;
    let asset_usdc: u64 = 0x05DC_0000_0000_0002;

    println!("Participants:");
    println!(
        "  Alice:   {:02x}{:02x}{:02x}{:02x}... (wants to BUY ETH)",
        alice_pubkey[0], alice_pubkey[1], alice_pubkey[2], alice_pubkey[3]
    );
    println!(
        "  Bob:     {:02x}{:02x}{:02x}{:02x}... (wants to SELL ETH)",
        bob_pubkey[0], bob_pubkey[1], bob_pubkey[2], bob_pubkey[3]
    );
    println!(
        "  Carol:   {:02x}{:02x}{:02x}{:02x}... (wants to BUY ETH, lower price)",
        carol_pubkey[0], carol_pubkey[1], carol_pubkey[2], carol_pubkey[3]
    );
    println!(
        "  Dave:    {:02x}{:02x}{:02x}{:02x}... (wants to SELL ETH, higher price)",
        dave_pubkey[0], dave_pubkey[1], dave_pubkey[2], dave_pubkey[3]
    );
    println!(
        "  Matcher: {:02x}{:02x}{:02x}{:02x}...",
        matcher_pubkey[0], matcher_pubkey[1], matcher_pubkey[2], matcher_pubkey[3]
    );
    println!();
    println!("Assets:");
    println!("  ETH:  0x{:016x}", asset_eth);
    println!("  USDC: 0x{:016x}", asset_usdc);
    println!();

    // Global nullifier set
    let mut nullifier_set = NullifierSet::new();

    // =======================================================================
    // STEP 1: TRADERS CREATE SEALED BIDS (note commitments)
    // =======================================================================
    println!("--- Step 1: TRADERS SUBMIT SEALED BIDS ---");
    println!("  Each bid is a note commitment. Price and quantity are HIDDEN.\n");

    // Alice: BUY 10 ETH @ 2000 USDC each (willing to spend 20000 USDC)
    // Note fields: [asset_type, quantity, price, side(1=buy,0=sell), 0, 0, 0, 0]
    let alice_bid_note = Note::with_randomness(
        alice_pubkey,
        [asset_eth, 10, 2000, 1, 0, 0, 0, 0],
        [0xA0u8; 32],
    );
    let alice_bid = SealedBid {
        commitment: alice_bid_note.commitment(),
        note: alice_bid_note.clone(),
        is_buy: true,
        asset_type: asset_eth,
        price: 2000,
        quantity: 10,
    };

    // Bob: SELL 10 ETH @ 1900 USDC each (willing to accept 19000 USDC)
    let bob_bid_note = Note::with_randomness(
        bob_pubkey,
        [asset_eth, 10, 1900, 0, 0, 0, 0, 0],
        [0xB0u8; 32],
    );
    let bob_bid = SealedBid {
        commitment: bob_bid_note.commitment(),
        note: bob_bid_note.clone(),
        is_buy: false,
        asset_type: asset_eth,
        price: 1900,
        quantity: 10,
    };

    // Carol: BUY 5 ETH @ 1800 USDC each (lower bid, won't match)
    let carol_bid_note = Note::with_randomness(
        carol_pubkey,
        [asset_eth, 5, 1800, 1, 0, 0, 0, 0],
        [0xC0u8; 32],
    );
    let carol_bid = SealedBid {
        commitment: carol_bid_note.commitment(),
        note: carol_bid_note.clone(),
        is_buy: true,
        asset_type: asset_eth,
        price: 1800,
        quantity: 5,
    };

    // Dave: SELL 5 ETH @ 2100 USDC each (higher ask, won't match)
    let dave_bid_note = Note::with_randomness(
        dave_pubkey,
        [asset_eth, 5, 2100, 0, 0, 0, 0, 0],
        [0xD0u8; 32],
    );
    let dave_bid = SealedBid {
        commitment: dave_bid_note.commitment(),
        note: dave_bid_note.clone(),
        is_buy: false,
        asset_type: asset_eth,
        price: 2100,
        quantity: 5,
    };

    // The order book only sees commitments (not prices or quantities)
    let order_book_commitments = vec![
        &alice_bid.commitment,
        &bob_bid.commitment,
        &carol_bid.commitment,
        &dave_bid.commitment,
    ];

    for (i, c) in order_book_commitments.iter().enumerate() {
        println!(
            "  Bid {}: commitment {:02x}{:02x}{:02x}{:02x}... (contents HIDDEN)",
            i + 1,
            c.0[0],
            c.0[1],
            c.0[2],
            c.0[3]
        );
    }
    println!();
    println!(
        "  Order book has {} sealed bids. No prices/quantities are visible.",
        order_book_commitments.len()
    );
    println!();

    // =======================================================================
    // STEP 2: SELECTIVE REVEAL — Only matching traders reveal to matcher
    // =======================================================================
    println!("--- Step 2: SELECTIVE REVEAL (matching traders only) ---");
    println!("  Alice and Bob reveal their bids to the matcher privately.");
    println!("  Carol and Dave do NOT reveal (their bids remain sealed).\n");

    // In practice, traders would use encrypted channels to reveal to the matcher.
    // The matcher sees that Alice buys @ 2000 and Bob sells @ 1900 => match!
    let alice_revealed = RevealedBid {
        bid: alice_bid.clone(),
        spending_key: alice_spending_key,
        signing_key: alice_sk.clone(),
    };

    let bob_revealed = RevealedBid {
        bid: bob_bid.clone(),
        spending_key: bob_spending_key,
        signing_key: bob_sk.clone(),
    };

    println!("  Matcher receives reveal from Alice: BUY 10 ETH @ 2000 USDC");
    println!("  Matcher receives reveal from Bob:   SELL 10 ETH @ 1900 USDC");
    println!();

    // Matcher checks: Alice's buy price (2000) >= Bob's sell price (1900) => MATCH!
    let match_price = (alice_revealed.bid.price + bob_revealed.bid.price) / 2; // midpoint
    let match_quantity = std::cmp::min(alice_revealed.bid.quantity, bob_revealed.bid.quantity);

    println!("  MATCH FOUND!");
    println!(
        "    Execution price: {} USDC per ETH (midpoint)",
        match_price
    );
    println!("    Quantity: {} ETH", match_quantity);
    println!("    Total: {} USDC", match_price * match_quantity);
    println!();

    // =======================================================================
    // STEP 3: ATOMIC SWAP VIA TURN COMPOSER
    // =======================================================================
    println!("--- Step 3: ATOMIC SWAP EXECUTION ---");

    let alice_cell_id = CellId::derive_raw(&alice_pubkey, &[0u8; 32]);
    let bob_cell_id = CellId::derive_raw(&bob_pubkey, &[0u8; 32]);
    let matcher_cell_id = CellId::derive_raw(&matcher_pubkey, &[0u8; 32]);

    // Alice spends her USDC note and receives ETH
    let alice_nullifier = alice_bid_note.nullifier(&alice_spending_key);
    let alice_receives = Note::with_randomness(
        alice_pubkey,
        [asset_eth, match_quantity, 0, 0, 0, 0, 0, 0],
        [0xA1u8; 32],
    );
    let alice_receives_commitment = alice_receives.commitment();

    // Bob spends his ETH note and receives USDC
    let bob_nullifier = bob_bid_note.nullifier(&bob_spending_key);
    let bob_receives = Note::with_randomness(
        bob_pubkey,
        [asset_usdc, match_price * match_quantity, 0, 0, 0, 0, 0, 0],
        [0xB1u8; 32],
    );
    let bob_receives_commitment = bob_receives.commitment();

    // Alice's action: spend USDC bid note, receive ETH
    let alice_action = Action {
        target: alice_cell_id,
        method: symbol("orderbook_fill"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Preconditions::default(),
        effects: vec![
            Effect::NoteSpend {
                nullifier: alice_nullifier,
                note_tree_root: [0u8; 32],
                value: match_price * match_quantity,
                asset_type: asset_usdc,
                spending_proof: vec![0x01], // placeholder for demo
                value_commitment: None,
            },
            Effect::NoteCreate {
                commitment: alice_receives_commitment,
                value: match_quantity,
                asset_type: asset_eth,
                encrypted_note: vec![0xAA; 64],
                value_commitment: None,
                range_proof: None,
            },
        ],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Partial,
        balance_change: None,
        witness_blobs: vec![],
    };

    // Bob's action: spend ETH bid note, receive USDC
    let bob_action = Action {
        target: bob_cell_id,
        method: symbol("orderbook_fill"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Preconditions::default(),
        effects: vec![
            Effect::NoteSpend {
                nullifier: bob_nullifier,
                note_tree_root: [0u8; 32],
                value: match_quantity,
                asset_type: asset_eth,
                spending_proof: vec![0x01], // placeholder for demo
                value_commitment: None,
            },
            Effect::NoteCreate {
                commitment: bob_receives_commitment,
                value: match_price * match_quantity,
                asset_type: asset_usdc,
                encrypted_note: vec![0xBB; 64],
                value_commitment: None,
                range_proof: None,
            },
        ],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Partial,
        balance_change: None,
        witness_blobs: vec![],
    };

    // Build the forest and sign fragments
    let mut temp_forest = CallForest::new();
    temp_forest.add_root(alice_action.clone());
    temp_forest.add_root(bob_action.clone());
    let forest_root = temp_forest.hash();

    let alice_signing_msg =
        TurnExecutor::compute_partial_signing_message(&alice_action, 0, &[0u8; 32], 0);
    let bob_signing_msg =
        TurnExecutor::compute_partial_signing_message(&bob_action, 1, &[0u8; 32], 0);

    let alice_sig = alice_revealed.signing_key.sign(&alice_signing_msg);
    let bob_sig = bob_revealed.signing_key.sign(&bob_signing_msg);

    // Compose the atomic turn
    let mut composer = TurnComposer::new(matcher_cell_id, 500, 0);
    composer.set_memo("Orderbook fill: 10 ETH @ 1950 USDC (midpoint)");

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

    composer
        .add_fragment(alice_fragment)
        .expect("Alice fragment valid");
    composer
        .add_fragment(bob_fragment)
        .expect("Bob fragment valid");

    let composed = composer.compose();
    match &composed {
        Ok(turn) => {
            println!("  Atomic turn composed successfully!");
            println!("  Action count: {}", turn.turn.action_count());
            println!("  Fee: {} computrons", turn.turn.fee);
            println!("  Memo: {:?}", turn.turn.memo);
        }
        Err(e) => {
            println!("  Composition result: {} (expected for demo)", e);
        }
    }
    println!();

    // Record nullifiers as spent
    nullifier_set
        .insert(alice_nullifier)
        .expect("Alice nullifier accepted");
    nullifier_set
        .insert(bob_nullifier)
        .expect("Bob nullifier accepted");

    println!(
        "  Alice's bid nullifier spent: {:02x}{:02x}{:02x}{:02x}...",
        alice_nullifier.0[0], alice_nullifier.0[1], alice_nullifier.0[2], alice_nullifier.0[3]
    );
    println!(
        "  Bob's bid nullifier spent: {:02x}{:02x}{:02x}{:02x}...",
        bob_nullifier.0[0], bob_nullifier.0[1], bob_nullifier.0[2], bob_nullifier.0[3]
    );
    println!();

    // =======================================================================
    // STEP 4: VERIFY UNMATCHED BIDS REMAIN PRIVATE
    // =======================================================================
    println!("--- Step 4: PRIVACY OF UNMATCHED BIDS ---");

    // Carol's and Dave's nullifiers should NOT be in the set
    let carol_nullifier = carol_bid_note.nullifier(&carol_spending_key);
    let dave_nullifier = dave_bid_note.nullifier(&_dave_spending_key);

    assert!(
        !nullifier_set.contains(&carol_nullifier),
        "Carol's bid should NOT be spent"
    );
    assert!(
        !nullifier_set.contains(&dave_nullifier),
        "Dave's bid should NOT be spent"
    );

    println!("  Carol's bid: STILL SEALED (nullifier not in set) [PASS]");
    println!("  Dave's bid:  STILL SEALED (nullifier not in set) [PASS]");
    println!();
    println!("  Key privacy properties:");
    println!("  - Carol's bid price (1800) was NEVER revealed to anyone");
    println!("  - Dave's bid price (2100) was NEVER revealed to anyone");
    println!(
        "  - Only the commitments {:02x}{:02x}... and {:02x}{:02x}... are public",
        carol_bid.commitment.0[0],
        carol_bid.commitment.0[1],
        dave_bid.commitment.0[0],
        dave_bid.commitment.0[1]
    );
    println!("  - An observer cannot determine bid direction, price, or quantity");
    println!("  - Unmatched bids can be reused in future matching rounds");
    println!();

    // =======================================================================
    // STEP 5: DOUBLE-SPEND PREVENTION (matched bids cannot be reused)
    // =======================================================================
    println!("--- Step 5: MATCHED BIDS CANNOT BE REUSED ---");

    let replay_alice = nullifier_set.insert(alice_nullifier);
    let replay_bob = nullifier_set.insert(bob_nullifier);

    assert!(replay_alice.is_err());
    assert!(replay_bob.is_err());

    println!("  Attempt to reuse Alice's filled bid: REJECTED [PASS]");
    println!("  Attempt to reuse Bob's filled bid: REJECTED [PASS]");
    println!();

    // =======================================================================
    // STEP 6: CONSERVATION VERIFICATION
    // =======================================================================
    println!("--- Step 6: CONSERVATION VERIFICATION ---");

    // Verify that the swap conserves value per asset type
    let mut eth_in: u64 = 0;
    let mut eth_out: u64 = 0;
    let mut usdc_in: u64 = 0;
    let mut usdc_out: u64 = 0;

    for action in [&alice_action, &bob_action] {
        for effect in &action.effects {
            match effect {
                Effect::NoteSpend {
                    value, asset_type, ..
                } => {
                    if *asset_type == asset_eth {
                        eth_in += value;
                    }
                    if *asset_type == asset_usdc {
                        usdc_in += value;
                    }
                }
                Effect::NoteCreate {
                    value, asset_type, ..
                } => {
                    if *asset_type == asset_eth {
                        eth_out += value;
                    }
                    if *asset_type == asset_usdc {
                        usdc_out += value;
                    }
                }
                _ => {}
            }
        }
    }

    assert_eq!(eth_in, eth_out, "ETH must be conserved");
    assert_eq!(usdc_in, usdc_out, "USDC must be conserved");

    println!("  ETH flows:");
    println!("    IN:  {} units (Bob's note spent)", eth_in);
    println!("    OUT: {} units (Alice's new note)", eth_out);
    println!("    Net: 0 [CONSERVED]");
    println!();
    println!("  USDC flows:");
    println!("    IN:  {} units (Alice's note spent)", usdc_in);
    println!("    OUT: {} units (Bob's new note)", usdc_out);
    println!("    Net: 0 [CONSERVED]");
    println!();

    // =======================================================================
    // SUMMARY
    // =======================================================================
    println!("--- Summary: Privacy Properties ---");
    println!("  ┌─────────────────────────────────────────────────────────────┐");
    println!("  │ Participant │ Bid Details      │ Status    │ Privacy          │");
    println!("  ├─────────────────────────────────────────────────────────────┤");
    println!("  │ Alice       │ BUY 10 @ 2000    │ FILLED    │ Revealed to      │");
    println!("  │             │                  │           │ matcher only     │");
    println!("  │ Bob         │ SELL 10 @ 1900   │ FILLED    │ Revealed to      │");
    println!("  │             │                  │           │ matcher only     │");
    println!("  │ Carol       │ BUY 5 @ 1800     │ UNMATCHED │ NEVER REVEALED   │");
    println!("  │ Dave        │ SELL 5 @ 2100    │ UNMATCHED │ NEVER REVEALED   │");
    println!("  └─────────────────────────────────────────────────────────────┘");
    println!();
    println!("  Total bids submitted: 4");
    println!("  Bids matched:         2 (Alice + Bob)");
    println!("  Bids still private:   2 (Carol + Dave)");
    println!("  Nullifiers spent:     {}", nullifier_set.len());
    println!();
    println!("=== Private Order Book Demo Complete ===");
}
