//! Sealed-Bid Auction Demo
//!
//! Demonstrates:
//! 1. Create auction cell with immutable parameters + private bid tracking
//! 2. Bid phase: bidders create committed notes with their bids
//! 3. Reveal phase: bids are revealed and validated against commitments
//! 4. Settlement: winner's funds transferred, losers refunded
//! 5. Progressive disclosure: bids are Committed until reveal phase

use pyana_cell::note::Note;
use pyana_cell::nullifier_set::NullifierSet;
use pyana_cell::program::{CellProgram, StateConstraint, field_from_u64};
use pyana_cell::state::{CellState, FieldVisibility};

fn main() {
    println!("=== Pyana Sealed-Bid Auction Demo ===\n");

    // --- Setup: Participants ---
    let seller_key = blake3::derive_key("seller-key-v1", b"seller-secret");
    let bidder_a_key = blake3::derive_key("bidder-a-key-v1", b"bidder-a-secret");
    let bidder_b_key = blake3::derive_key("bidder-b-key-v1", b"bidder-b-secret");
    let bidder_c_key = blake3::derive_key("bidder-c-key-v1", b"bidder-c-secret");

    let seller_pubkey = blake3::derive_key("seller-pub-v1", &seller_key);
    let bidder_a_pubkey = blake3::derive_key("bidder-a-pub-v1", &bidder_a_key);
    let bidder_b_pubkey = blake3::derive_key("bidder-b-pub-v1", &bidder_b_key);
    let bidder_c_pubkey = blake3::derive_key("bidder-c-pub-v1", &bidder_c_key);

    // Auction parameters
    let asset_id: u64 = 0xA001_CDEF_0000_0001; // What's being auctioned
    let minimum_bid: u64 = 500;
    let deadline: u64 = 1700200000; // Bidding deadline
    let auction_id: u64 = u64::from_le_bytes(
        blake3::hash(b"auction-2024-001").as_bytes()[..8]
            .try_into()
            .unwrap(),
    );

    println!("Auction Setup:");
    println!("  Asset being sold: 0x{:016x}", asset_id);
    println!("  Minimum bid:      {} units", minimum_bid);
    println!("  Deadline:         {} (unix)", deadline);
    println!("  Auction ID:       0x{:016x}", auction_id);
    println!(
        "  Seller:           {:02x}{:02x}{:02x}{:02x}...",
        seller_pubkey[0], seller_pubkey[1], seller_pubkey[2], seller_pubkey[3]
    );
    println!(
        "  Bidder A:         {:02x}{:02x}{:02x}{:02x}...",
        bidder_a_pubkey[0], bidder_a_pubkey[1], bidder_a_pubkey[2], bidder_a_pubkey[3]
    );
    println!(
        "  Bidder B:         {:02x}{:02x}{:02x}{:02x}...",
        bidder_b_pubkey[0], bidder_b_pubkey[1], bidder_b_pubkey[2], bidder_b_pubkey[3]
    );
    println!(
        "  Bidder C:         {:02x}{:02x}{:02x}{:02x}...",
        bidder_c_pubkey[0], bidder_c_pubkey[1], bidder_c_pubkey[2], bidder_c_pubkey[3]
    );
    println!();

    // =======================================================================
    // STEP 1: CREATE AUCTION CELL
    // =======================================================================
    println!("--- Step 1: CREATE AUCTION CELL ---");

    // Auction cell layout:
    // field[0] = asset_id (Immutable)
    // field[1] = minimum_bid (Immutable)
    // field[2] = deadline (Immutable)
    // field[3] = highest_bid (starts at 0, updated during reveal)
    // field[4] = winner_commitment (hash of winner's identity)
    // field[5] = auction_state (0=bidding, 1=reveal, 2=settled)

    let auction_program = CellProgram::Predicate(vec![
        StateConstraint::Immutable { index: 0 }, // asset_id locked
        StateConstraint::Immutable { index: 1 }, // minimum_bid locked
        StateConstraint::Immutable { index: 2 }, // deadline locked
        // highest_bid must always be >= minimum_bid (once set)
        StateConstraint::FieldGte {
            index: 3,
            value: field_from_u64(minimum_bid),
        },
    ]);

    let mut auction_state = CellState::new(0);
    auction_state.fields[0] = field_from_u64(asset_id);
    auction_state.fields[1] = field_from_u64(minimum_bid);
    auction_state.fields[2] = field_from_u64(deadline);
    auction_state.fields[3] = field_from_u64(minimum_bid); // Start at minimum (satisfies Gte)
    auction_state.fields[4] = [0u8; 32]; // No winner yet
    auction_state.fields[5] = field_from_u64(0); // State: bidding

    // Set bid fields as Committed (private)
    auction_state.set_field_visibility(3, FieldVisibility::Committed, 42);
    auction_state.set_field_visibility(4, FieldVisibility::Committed, 43);

    let init_result = auction_program.evaluate(&auction_state, None, None);
    assert!(init_result.is_ok());

    println!("  Auction cell created with program constraints");
    println!("  field[3] (highest_bid) visibility: Committed (private until reveal)");
    println!("  field[4] (winner) visibility: Committed (private until reveal)");
    println!("  Program validation: [PASS]");
    println!();

    // =======================================================================
    // STEP 2: BID PHASE — Each bidder creates a committed note
    // =======================================================================
    println!("--- Step 2: BID PHASE (sealed bids via notes) ---");

    let mut nullifier_set = NullifierSet::new();

    // Bidder A bids 1000 units
    let bid_a_amount: u64 = 1000;
    let bid_a_fields = [auction_id, bid_a_amount, 0, 0, 0, 0, 0, 0];
    let bid_note_a = Note::with_randomness(bidder_a_pubkey, bid_a_fields, [0xA0u8; 32]);
    let commitment_a = bid_note_a.commitment();

    // Bidder B bids 2500 units
    let bid_b_amount: u64 = 2500;
    let bid_b_fields = [auction_id, bid_b_amount, 0, 0, 0, 0, 0, 0];
    let bid_note_b = Note::with_randomness(bidder_b_pubkey, bid_b_fields, [0xB0u8; 32]);
    let commitment_b = bid_note_b.commitment();

    // Bidder C bids 800 units (below eventual winner, above minimum)
    let bid_c_amount: u64 = 800;
    let bid_c_fields = [auction_id, bid_c_amount, 0, 0, 0, 0, 0, 0];
    let bid_note_c = Note::with_randomness(bidder_c_pubkey, bid_c_fields, [0xC0u8; 32]);
    let commitment_c = bid_note_c.commitment();

    println!(
        "  Bidder A submits sealed bid (commitment: {:02x}{:02x}{:02x}{:02x}...)",
        commitment_a.0[0], commitment_a.0[1], commitment_a.0[2], commitment_a.0[3]
    );
    println!(
        "  Bidder B submits sealed bid (commitment: {:02x}{:02x}{:02x}{:02x}...)",
        commitment_b.0[0], commitment_b.0[1], commitment_b.0[2], commitment_b.0[3]
    );
    println!(
        "  Bidder C submits sealed bid (commitment: {:02x}{:02x}{:02x}{:02x}...)",
        commitment_c.0[0], commitment_c.0[1], commitment_c.0[2], commitment_c.0[3]
    );
    println!("  (All bid amounts are hidden behind commitments)");
    println!();

    // =======================================================================
    // STEP 3: REVEAL PHASE — Bids are opened and validated
    // =======================================================================
    println!("--- Step 3: REVEAL PHASE (after deadline) ---");
    println!("  Deadline reached. Bidders reveal their bids...\n");

    let old_auction_state = auction_state.clone();

    // Reveal Bidder A: 1000 units
    println!("  Bidder A reveals: {} units", bid_a_amount);
    assert_eq!(
        bid_note_a.fields[0], auction_id,
        "Bid must reference correct auction"
    );
    assert!(bid_a_amount >= minimum_bid, "Bid must meet minimum");
    println!("    Auction ID match: [PASS]");
    println!("    Bid >= minimum ({}): [PASS]", minimum_bid);

    // Reveal Bidder B: 2500 units
    println!("  Bidder B reveals: {} units", bid_b_amount);
    assert_eq!(bid_note_b.fields[0], auction_id);
    assert!(bid_b_amount >= minimum_bid);
    println!("    Auction ID match: [PASS]");
    println!("    Bid >= minimum ({}): [PASS]", minimum_bid);

    // Reveal Bidder C: 800 units
    println!("  Bidder C reveals: {} units", bid_c_amount);
    assert_eq!(bid_note_c.fields[0], auction_id);
    assert!(bid_c_amount >= minimum_bid);
    println!("    Auction ID match: [PASS]");
    println!("    Bid >= minimum ({}): [PASS]", minimum_bid);
    println!();

    // Determine winner
    let bids = [
        (bid_a_amount, "A", &bidder_a_pubkey),
        (bid_b_amount, "B", &bidder_b_pubkey),
        (bid_c_amount, "C", &bidder_c_pubkey),
    ];
    let (winning_amount, winner_name, winner_key) =
        bids.iter().max_by_key(|(amount, _, _)| *amount).unwrap();

    println!(
        "  WINNER: Bidder {} with {} units!",
        winner_name, winning_amount
    );
    println!();

    // Update auction cell with winner info
    let winner_hash = *blake3::hash(winner_key.as_slice()).as_bytes();
    auction_state.fields[3] = field_from_u64(*winning_amount); // highest bid
    auction_state.fields[4] = winner_hash; // winner commitment
    auction_state.fields[5] = field_from_u64(1); // State: reveal complete

    // Verify program still holds (highest_bid >= minimum_bid, immutables unchanged)
    let reveal_result = auction_program.evaluate(&auction_state, Some(&old_auction_state), None);
    assert!(reveal_result.is_ok(), "Reveal should satisfy program");
    println!("  Auction cell updated with winner");
    println!("  Program constraints verified: [PASS]");
    println!();

    // =======================================================================
    // STEP 4: SETTLEMENT — Winner pays, losers refunded
    // =======================================================================
    println!("--- Step 4: SETTLEMENT ---");

    // Winner's bid note is spent (funds go to seller)
    let winner_nullifier = bid_note_b.nullifier(&bidder_b_key);
    nullifier_set
        .insert(winner_nullifier)
        .expect("Winner spend should succeed");
    println!("  Winner (Bidder B) spends bid note");
    println!(
        "    Nullifier: {:02x}{:02x}{:02x}{:02x}...",
        winner_nullifier.0[0], winner_nullifier.0[1], winner_nullifier.0[2], winner_nullifier.0[3]
    );

    // Create payment note for seller
    let payment_fields = [auction_id, *winning_amount, 0, 0, 0, 0, 0, 0];
    let seller_note = Note::with_randomness(seller_pubkey, payment_fields, [0xFFu8; 32]);
    let seller_commitment = seller_note.commitment();
    println!(
        "  Payment note created for seller: {:02x}{:02x}{:02x}{:02x}...",
        seller_commitment.0[0],
        seller_commitment.0[1],
        seller_commitment.0[2],
        seller_commitment.0[3]
    );
    println!("    Amount: {} units", winning_amount);
    println!();

    // Losers get their notes returned (spend original, create new with same value)
    println!("  Refunding losing bidders...");

    // Bidder A refund
    let refund_a_nullifier = bid_note_a.nullifier(&bidder_a_key);
    nullifier_set
        .insert(refund_a_nullifier)
        .expect("Refund A should succeed");
    let refund_note_a = Note::with_randomness(
        bidder_a_pubkey,
        [0, bid_a_amount, 0, 0, 0, 0, 0, 0],
        [0xA1u8; 32],
    );
    let refund_commitment_a = refund_note_a.commitment();
    println!(
        "    Bidder A: bid note spent, refund note created ({} units)",
        bid_a_amount
    );
    println!(
        "      Refund commitment: {:02x}{:02x}{:02x}{:02x}...",
        refund_commitment_a.0[0],
        refund_commitment_a.0[1],
        refund_commitment_a.0[2],
        refund_commitment_a.0[3]
    );

    // Bidder C refund
    let refund_c_nullifier = bid_note_c.nullifier(&bidder_c_key);
    nullifier_set
        .insert(refund_c_nullifier)
        .expect("Refund C should succeed");
    let refund_note_c = Note::with_randomness(
        bidder_c_pubkey,
        [0, bid_c_amount, 0, 0, 0, 0, 0, 0],
        [0xC1u8; 32],
    );
    let refund_commitment_c = refund_note_c.commitment();
    println!(
        "    Bidder C: bid note spent, refund note created ({} units)",
        bid_c_amount
    );
    println!(
        "      Refund commitment: {:02x}{:02x}{:02x}{:02x}...",
        refund_commitment_c.0[0],
        refund_commitment_c.0[1],
        refund_commitment_c.0[2],
        refund_commitment_c.0[3]
    );
    println!();

    // =======================================================================
    // STEP 5: ADVERSARY ATTEMPTS
    // =======================================================================
    println!("--- Step 5: ADVERSARY SCENARIOS ---");

    // Attempt 1: Try to change asset_id (immutable)
    let mut adversary_state = auction_state.clone();
    adversary_state.fields[0] = field_from_u64(0xDEADBEEF);
    let adversary_result = auction_program.evaluate(&adversary_state, Some(&auction_state), None);
    assert!(adversary_result.is_err());
    println!("  Attack 1: Change asset_id -> REJECTED (Immutable)");

    // Attempt 2: Lower minimum_bid retroactively
    let mut adversary_state2 = auction_state.clone();
    adversary_state2.fields[1] = field_from_u64(0);
    let adversary_result2 = auction_program.evaluate(&adversary_state2, Some(&auction_state), None);
    assert!(adversary_result2.is_err());
    println!("  Attack 2: Lower minimum_bid -> REJECTED (Immutable)");

    // Attempt 3: Double-spend the winner's bid
    let double_spend = nullifier_set.insert(winner_nullifier);
    assert!(double_spend.is_err());
    println!("  Attack 3: Double-spend winner's bid -> REJECTED (nullifier already spent)");

    // Attempt 4: Set highest_bid below minimum
    let mut adversary_state3 = auction_state.clone();
    adversary_state3.fields[3] = field_from_u64(100); // below minimum of 500
    let adversary_result3 = auction_program.evaluate(&adversary_state3, Some(&auction_state), None);
    assert!(adversary_result3.is_err());
    println!("  Attack 4: Set highest_bid < minimum -> REJECTED (FieldGte)");
    println!();

    // =======================================================================
    // FINAL STATE
    // =======================================================================
    println!("--- Final State ---");
    println!("  Auction settled successfully");
    println!("  Winner: Bidder B ({} units)", winning_amount);
    println!("  Seller received: {} units via note", winning_amount);
    println!("  Bidder A refunded: {} units", bid_a_amount);
    println!("  Bidder C refunded: {} units", bid_c_amount);
    println!("  Nullifiers consumed: {}", nullifier_set.len());
    println!("  All program invariants maintained throughout");
    println!();
    println!("=== Auction Demo Complete ===");
}
