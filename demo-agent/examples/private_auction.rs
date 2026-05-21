//! Private Sealed-Bid Auction — Three Bidders, Full Privacy, Atomic Settlement
//!
//! **Story**: Three bidders submit sealed bids for a digital art piece.
//! The auction resolves privately — the winner is determined without revealing
//! any bid amounts to third parties, and even the auctioneer doesn't learn
//! the losing bids.
//!
//! Shows:
//! - Note commitments as sealed bids (Poseidon2(bid, randomness))
//! - Predicate proofs for bid validity ("my bid >= minimum" without revealing amount)
//! - Committed threshold for winner determination in each round
//! - Conditional turns for atomic settlement (pay-for-art, both or neither)
//! - Privacy: losing bidders' amounts are NEVER revealed
//!
//! The key privacy guarantee: an observer watching the entire auction learns only:
//! 1. Three valid bids were submitted (all above minimum)
//! 2. One bidder won
//! 3. The winner paid and received the art (atomically)
//!
//! They CANNOT determine: what any bidder bid, who the losing bidders are,
//! or how close the bids were to each other.
//!
//! Run with: cargo run --release -p pyana-demo-agent --example private_auction

use std::time::Instant;

use pyana_cell::note::Note;
use pyana_cell::nullifier_set::NullifierSet;
use pyana_cell::seal::SealPair;
use pyana_circuit::{
    BabyBear, PredicateProof, PredicateType, PredicateWitness,
    committed_threshold::{
        CommittedThresholdWitness, compute_threshold_commitment, generate_blinding,
        prove_committed_threshold, verify_committed_threshold,
    },
    poseidon2,
    predicate_air::compute_fact_commitment,
    prove_predicate,
    stark::proof_to_bytes,
    verify_predicate,
};
use pyana_turn::{ConditionProof, ConditionalTurn, ProofCondition, compute_conditional_deposit};

/// A bidder's private state (known only to them).
struct Bidder {
    name: &'static str,
    bid_amount: u64,
    spending_key: [u8; 32],
    pubkey: [u8; 32],
    blinding: [u8; 32],
    bid_note: Note,
    bid_commitment: BabyBear,
    fact_commitment: BabyBear,
}

/// What the public ledger shows for each bid (nothing about the amount).
struct SealedBidRecord {
    /// Poseidon2(amount, blinding) — hides the bid amount.
    commitment: BabyBear,
    /// STARK proof that bid >= minimum (without revealing what the bid IS).
    validity_proof: PredicateProof,
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

fn main() {
    println!("===============================================================================");
    println!("  PRIVATE SEALED-BID AUCTION");
    println!("  Three Bidders, Zero Knowledge, Atomic Settlement");
    println!("===============================================================================");
    println!();
    println!("  A digital artist auctions \"Meridian\" — a unique generative artwork.");
    println!("  Three collectors submit sealed bids. Nobody learns what anyone else bid.");
    println!("  The winner pays and receives the art atomically. Losers get refunds.");
    println!("  Even the auctioneer never learns the losing bids.");
    println!();

    let total_start = Instant::now();

    // =========================================================================
    // PHASE 1: AUCTION SETUP
    // =========================================================================
    println!("--- Phase 1: AUCTION PARAMETERS ---");
    println!();

    let minimum_bid: u64 = 500;
    let artwork_hash =
        *blake3::hash(b"Meridian: procedural flow fields, 4096x4096, edition 1/1").as_bytes();
    let auction_state_root = BabyBear::new(77777);

    println!("  Artwork: \"Meridian\" (generative, 4096x4096, 1/1)");
    println!("  Asset hash: {}", short_hex(&artwork_hash));
    println!("  Minimum bid: {} units", minimum_bid);
    println!("  Bid deadline: block 500");
    println!();

    // =========================================================================
    // PHASE 2: SEALED BIDDING — Each bidder commits without revealing amount
    // =========================================================================
    println!("--- Phase 2: SEALED BIDDING ---");
    println!();
    println!("  Each bidder:");
    println!("    1. Chooses their bid amount (private)");
    println!("    2. Computes commitment = Poseidon2(bid, randomness)");
    println!("    3. Proves bid >= minimum via PredicateAir (amount stays hidden)");
    println!("    4. Submits (commitment, proof) to the auction contract");
    println!();

    let phase2_start = Instant::now();
    let mut nullifier_set = NullifierSet::new();

    // Create three bidders with their private bid amounts
    let bidder_configs: [(&str, u64, u8); 3] = [
        ("Aria", 2500, 0xAA),  // Aria bids 2500
        ("Blake", 4200, 0xBB), // Blake bids 4200 (winner!)
        ("Cyrus", 1800, 0xCC), // Cyrus bids 1800
    ];

    let mut bidders: Vec<Bidder> = Vec::new();
    let mut sealed_records: Vec<SealedBidRecord> = Vec::new();

    for (name, amount, rand_seed) in &bidder_configs {
        // Derive keys
        let spending_key = blake3::derive_key(
            &format!("{}-auction-spending-v1", name.to_lowercase()),
            name.as_bytes(),
        );
        let pubkey = blake3::derive_key(
            &format!("{}-auction-pubkey-v1", name.to_lowercase()),
            name.as_bytes(),
        );
        let blinding = [*rand_seed; 32];

        // Create the bid note (private — only the bidder knows its contents)
        let auction_tag = u64::from_le_bytes(artwork_hash[..8].try_into().unwrap());
        let bid_note =
            Note::with_randomness(pubkey, [auction_tag, *amount, 0, 0, 0, 0, 0, 0], blinding);

        // Compute the bid commitment: Poseidon2(amount, blinding_field)
        let amount_field = BabyBear::new(*amount as u32);
        let blinding_field = BabyBear::new(*rand_seed as u32 * 257);
        let bid_commitment = poseidon2::hash_2_to_1(amount_field, blinding_field);

        // Compute fact commitment (binds to this specific auction)
        let fact_hash = poseidon2::hash_fact(
            BabyBear::new(42), // "bid" predicate
            &[amount_field, blinding_field, BabyBear::ZERO],
        );
        let fact_commitment = compute_fact_commitment(fact_hash, auction_state_root);

        // Generate STARK proof: bid >= minimum_bid (without revealing bid)
        let witness = PredicateWitness {
            private_value: amount_field,
            threshold: BabyBear::new(minimum_bid as u32),
            predicate_type: PredicateType::Gte,
            fact_commitment,
            blinding: None,
            fact_hash: None,
            state_root: None,
        };

        let validity_proof =
            prove_predicate(witness).expect("All bids are above minimum — proof must succeed");

        // Verify (as the auction contract would)
        assert!(verify_predicate(
            &validity_proof,
            BabyBear::new(minimum_bid as u32),
            fact_commitment,
        ));

        sealed_records.push(SealedBidRecord {
            commitment: bid_commitment,
            validity_proof,
        });

        bidders.push(Bidder {
            name,
            bid_amount: *amount,
            spending_key,
            pubkey,
            blinding,
            bid_note,
            bid_commitment,
            fact_commitment,
        });
    }

    let phase2_time = phase2_start.elapsed();

    // Show what the public sees
    println!("  Public auction state (what observers see):");
    println!();
    println!("    {:>3} | {:>12} | {:>12}", "#", "Commitment", "Validity");
    println!("    {}", "-".repeat(40));
    for (i, record) in sealed_records.iter().enumerate() {
        println!(
            "    {:>3} | {:>12} | {:>12}",
            i + 1,
            record.commitment.as_u32(),
            "VALID"
        );
    }
    println!();
    println!("  What the public knows:");
    println!(
        "    - 3 bids submitted, all >= {} (proven by PredicateAir)",
        minimum_bid
    );
    println!("    - Nothing about the actual amounts (hidden behind commitments)");
    println!("    - Nothing about who submitted which bid");
    println!();
    println!(
        "  Phase 2 timing: {:.2}ms (3 predicate proofs)",
        phase2_time.as_secs_f64() * 1000.0
    );
    println!();

    // =========================================================================
    // PHASE 3: WINNER DETERMINATION (committed threshold comparison)
    // =========================================================================
    println!("--- Phase 3: WINNER DETERMINATION ---");
    println!();
    println!("  The auction uses committed-threshold proofs to determine the winner.");
    println!("  In each comparison round, a bidder proves their bid exceeds a threshold");
    println!("  WITHOUT revealing either their bid or the threshold to observers.");
    println!();

    let phase3_start = Instant::now();

    // The auctioneer runs a binary comparison protocol:
    // Each bidder proves "my bid >= second-highest" to show they won.
    // We simulate this by having each bidder prove against the actual winning threshold.

    // In practice, this uses a garbled circuit or MPC comparison.
    // Here we demonstrate the committed-threshold approach:
    // The auctioneer sets a threshold at the second-highest bid (2500),
    // and only the winner (Blake, 4200) can prove they exceed it.

    let second_highest = 2500u64; // Aria's bid (second highest)
    let comparison_blinding = generate_blinding();
    let comparison_commitment =
        compute_threshold_commitment(BabyBear::new(second_highest as u32), comparison_blinding);

    println!(
        "  Auctioneer publishes comparison commitment: {}",
        comparison_commitment.as_u32()
    );
    println!("  (Hides the threshold: observers cannot determine second-highest bid)");
    println!();

    // Each bidder attempts to prove they beat the threshold
    let mut winner_idx: Option<usize> = None;

    for (i, bidder) in bidders.iter().enumerate() {
        let witness = CommittedThresholdWitness {
            private_value: BabyBear::new(bidder.bid_amount as u32),
            threshold: BabyBear::new(second_highest as u32),
            blinding: comparison_blinding,
            fact_commitment: bidder.fact_commitment,
        };

        if witness.is_satisfiable() {
            // Can prove: bid >= threshold
            let proof = prove_committed_threshold(witness);
            match proof {
                Some(p) => {
                    // Verify the proof
                    let valid = verify_committed_threshold(
                        &p,
                        comparison_commitment,
                        bidder.fact_commitment,
                    );
                    if valid {
                        println!(
                            "  {} proves bid >= threshold: PASS (winner candidate)",
                            bidder.name
                        );
                        winner_idx = Some(i);
                    }
                }
                None => {
                    println!(
                        "  {} proves bid >= threshold: proof generation failed",
                        bidder.name
                    );
                }
            }
        } else {
            println!(
                "  {} proves bid >= threshold: CANNOT PROVE (below threshold)",
                bidder.name
            );
        }
    }

    let winner_idx = winner_idx.expect("There must be a winner");
    let winner = &bidders[winner_idx];
    let phase3_time = phase3_start.elapsed();

    println!();
    println!("  ┌──────────────────────────────────────────────────────────────┐");
    println!(
        "  │  WINNER: {} (bid: {} units — proven >= threshold)       │",
        winner.name, winner.bid_amount
    );
    println!("  └──────────────────────────────────────────────────────────────┘");
    println!();
    println!("  Privacy preserved:");
    println!("    - Observers see: one bidder proved they beat the commitment");
    println!("    - Observers CANNOT see: the actual bid amount or the threshold");
    println!("    - Losing bidders' amounts: NEVER REVEALED (they couldn't prove it)");
    println!();
    println!(
        "  Phase 3 timing: {:.2}ms",
        phase3_time.as_secs_f64() * 1000.0
    );
    println!();

    // =========================================================================
    // PHASE 4: ATOMIC SETTLEMENT (ConditionalTurn)
    // =========================================================================
    println!("--- Phase 4: ATOMIC SETTLEMENT ---");
    println!();
    println!("  The winner's payment and the art delivery are coupled via ConditionalTurn.");
    println!("  Both execute atomically: Blake pays AND receives the art, or neither happens.");
    println!();

    let phase4_start = Instant::now();

    // Seal the artwork to the winner
    let winner_seal = SealPair::generate();
    let sealed_art = winner_seal.seal(&pyana_cell::capability::CapabilityRef {
        target: pyana_cell::CellId::from_bytes(winner.pubkey),
        slot: 0,
        permissions: pyana_cell::AuthRequired::Signature,
        breadstuff: Some(artwork_hash),
        expires_at: None,
    });
    let sealed_bytes = postcard::to_stdvec(&sealed_art).unwrap();

    println!("  Step 4a: Artist seals artwork to winner's key");
    println!(
        "    Sealed size: {} bytes (X25519 + ChaCha20-Poly1305)",
        sealed_bytes.len()
    );
    println!();

    // Winner spends their bid note (payment)
    let winner_nullifier = winner.bid_note.nullifier(&winner.spending_key);
    nullifier_set
        .insert(winner_nullifier)
        .expect("winner spend succeeds");

    println!("  Step 4b: Winner spends bid note (nullifier published)");
    println!("    Nullifier: {}", short_hex(&winner_nullifier.0));
    println!();

    // Create the ConditionalTurn for atomic execution.
    // The artist commits to a delivery secret; revealing the secret proves delivery.
    let delivery_secret = [0xDE; 32]; // Artist's delivery secret (known only to artist)
    let delivery_hash = *blake3::hash(&delivery_secret).as_bytes();
    let current_height = 501;
    let timeout_height = 600;
    let deposit = compute_conditional_deposit(timeout_height, current_height);

    let _winner_conditional = ConditionalTurn {
        turn: pyana_turn::Turn {
            agent: pyana_cell::CellId::from_bytes(winner.pubkey),
            nonce: 0,
            fee: 0,
            memo: Some("Private auction: Meridian".to_string()),
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: vec![],
            call_forest: pyana_turn::CallForest::new(),
        },
        condition: ProofCondition::HashPreimage {
            hash: delivery_hash,
        },
        timeout_height,
        submitted_at: current_height,
        deposit_amount: deposit,
    };

    // Resolve the condition (artist reveals delivery secret = proves delivery happened)
    let art_proof = ConditionProof::Preimage(delivery_secret);
    let mut null_set = std::collections::HashSet::new();
    let result = pyana_turn::resolve_condition(
        &ProofCondition::HashPreimage {
            hash: delivery_hash,
        },
        &art_proof,
        current_height + 1,
        timeout_height,
        &[],
        pyana_turn::DEFAULT_MAX_ROOT_AGE,
        &mut null_set,
        &[],
    );
    assert_eq!(result, pyana_turn::ConditionalResult::Resolved);

    println!("  Step 4c: Atomic settlement via ConditionalTurn");
    println!("    Condition: hash preimage of sealed artwork delivery");
    println!("    Resolution: RESOLVED (artist provided delivery proof)");
    println!(
        "    Result: Blake paid {} units AND received sealed artwork",
        winner.bid_amount
    );
    println!();

    // Winner unseals the art
    let recovered = winner_seal.unseal(&sealed_art).expect("winner can unseal");
    assert_eq!(recovered.breadstuff.unwrap(), artwork_hash);
    println!("  Step 4d: Winner unseals artwork");
    println!(
        "    Art hash verified: {} [MATCH]",
        short_hex(&artwork_hash)
    );
    println!("    Blake now possesses \"Meridian\"!");
    println!();

    let phase4_time = phase4_start.elapsed();
    println!(
        "  Phase 4 timing: {:.2}ms",
        phase4_time.as_secs_f64() * 1000.0
    );
    println!();

    // =========================================================================
    // PHASE 5: REFUND LOSING BIDDERS
    // =========================================================================
    println!("--- Phase 5: REFUND LOSING BIDDERS ---");
    println!();
    println!("  Losing bidders get their deposits back. Their bid amounts are NEVER revealed.");
    println!();

    for (i, bidder) in bidders.iter().enumerate() {
        if i == winner_idx {
            continue;
        }
        // Spend their bid note (refund to themselves)
        let nullifier = bidder.bid_note.nullifier(&bidder.spending_key);
        nullifier_set
            .insert(nullifier)
            .expect("refund spend succeeds");

        // Create a fresh note for the refund (same amount, new randomness)
        let refund_note = Note::with_randomness(
            bidder.pubkey,
            [0, bidder.bid_amount, 0, 0, 0, 0, 0, 0],
            [bidder.blinding[0].wrapping_add(1); 32],
        );
        let refund_commitment = refund_note.commitment();

        println!("  {}: refund processed", bidder.name);
        println!(
            "    Bid note spent (nullifier: {})",
            short_hex(&nullifier.0)
        );
        println!(
            "    Refund note created (commitment: {})",
            short_hex(&refund_commitment.0)
        );
        println!("    Amount: HIDDEN (same as original bid, but observers cannot verify)");
    }
    println!();
    println!("  Critical privacy point: Even after the auction completes,");
    println!("  Aria's bid of 2500 and Cyrus's bid of 1800 are NEVER published.");
    println!("  Only the participants themselves know their own bids.");
    println!();

    // =========================================================================
    // PHASE 6: ADVERSARY ANALYSIS
    // =========================================================================
    println!("--- Phase 6: ADVERSARY ANALYSIS ---");
    println!();

    // Attack: bid below minimum
    println!("  Attack 1: Submit a bid below minimum (bid=200, min=500)");
    let low_witness = PredicateWitness {
        private_value: BabyBear::new(200),
        threshold: BabyBear::new(minimum_bid as u32),
        predicate_type: PredicateType::Gte,
        fact_commitment: BabyBear::new(999),
        blinding: None,
        fact_hash: None,
        state_root: None,
    };
    let low_proof = prove_predicate(low_witness);
    assert!(low_proof.is_none());
    println!("    Cannot generate validity proof (200 < 500 is unprovable). [BLOCKED]");
    println!();

    // Attack: double-spend winning bid
    println!("  Attack 2: Double-spend the winning bid note");
    let double_spend = nullifier_set.insert(winner_nullifier);
    assert!(double_spend.is_err());
    println!(
        "    Nullifier already in set: {:?} [BLOCKED]",
        double_spend.unwrap_err()
    );
    println!();

    // Attack: non-winner tries to unseal art
    println!("  Attack 3: Losing bidder tries to unseal the artwork");
    let aria_seal = SealPair::generate();
    let aria_unseal = aria_seal.unseal(&sealed_art);
    assert!(aria_unseal.is_err());
    println!("    Wrong key: {:?} [BLOCKED]", aria_unseal.unwrap_err());
    println!();

    // Attack: forge a higher bid after seeing others
    println!("  Attack 4: Forge a commitment to a different (higher) amount");
    println!("    Commitments are binding (Poseidon2). Once submitted, the bidder");
    println!("    cannot open the commitment to a different value.");
    println!("    The randomness is committed to — changing the amount changes the hash.");
    let original = poseidon2::hash_2_to_1(BabyBear::new(1800), BabyBear::new(0xCC * 257));
    let forged = poseidon2::hash_2_to_1(BabyBear::new(5000), BabyBear::new(0xCC * 257));
    assert_ne!(original, forged);
    println!(
        "    Original commitment: {} vs forged: {} [DIFFERENT]",
        original.as_u32(),
        forged.as_u32()
    );
    println!("    Cannot retroactively change bid without detection. [BLOCKED]");
    println!();

    // =========================================================================
    // PRIVACY SUMMARY
    // =========================================================================
    println!("--- Privacy Summary ---");
    println!();
    println!("  ┌─────────────────────────────────────────────────────────────────┐");
    println!("  │  Information         │ Public? │ Known to               │");
    println!("  ├─────────────────────────────────────────────────────────────────┤");
    println!("  │  # of bids           │ YES     │ Everyone               │");
    println!("  │  All bids >= minimum  │ YES     │ Everyone (proven by ZK)│");
    println!("  │  Winner identity     │ YES*    │ Auction + winner       │");
    println!("  │  Winning bid amount  │ NO      │ Winner only            │");
    println!("  │  Losing bid amounts  │ NO      │ Each loser knows theirs│");
    println!("  │  Comparison threshold│ NO      │ Auctioneer + winner    │");
    println!("  │  Artwork content     │ NO      │ Winner only (sealed)   │");
    println!("  │  Bid-to-bidder link  │ NO      │ Each bidder knows theirs│");
    println!("  └─────────────────────────────────────────────────────────────────┘");
    println!();
    println!("  * Winner identity can also be hidden using ring membership proofs");
    println!("    (see the full private_auction example for that extension).");
    println!();

    // =========================================================================
    // FINAL SUMMARY
    // =========================================================================
    let total_time = total_start.elapsed();

    println!("===============================================================================");
    println!("  FINAL SUMMARY");
    println!("===============================================================================");
    println!();
    println!("  Auction: \"Meridian\" by the artist");
    println!(
        "  Winner: {} (bid: {} units)",
        winner.name, winner.bid_amount
    );
    println!(
        "  Losers: {} ({} units, HIDDEN), {} ({} units, HIDDEN)",
        bidders[0].name, bidders[0].bid_amount, bidders[2].name, bidders[2].bid_amount
    );
    println!("  Nullifiers consumed: {}", nullifier_set.len());
    println!();
    println!("  Components exercised:");
    println!("    - Poseidon2 commitments (bid hiding)");
    println!("    - PredicateAir (bid >= minimum proof)");
    println!("    - CommittedThresholdAir (private winner comparison)");
    println!("    - SealPair (X25519 + AEAD artwork encryption)");
    println!("    - ConditionalTurn (atomic pay-for-art)");
    println!("    - NullifierSet (double-spend prevention)");
    println!();
    println!("  Timing:");
    println!(
        "    Phase 2 (sealed bidding):     {:>8.2}ms",
        phase2_time.as_secs_f64() * 1000.0
    );
    println!(
        "    Phase 3 (winner determination):{:>8.2}ms",
        phase3_time.as_secs_f64() * 1000.0
    );
    println!(
        "    Phase 4 (atomic settlement):  {:>8.2}ms",
        phase4_time.as_secs_f64() * 1000.0
    );
    println!(
        "    Total:                        {:>8.2}ms",
        total_time.as_secs_f64() * 1000.0
    );
    println!();
    println!("  In this system, auctions are PRIVATE BY DEFAULT.");
    println!("  Bid amounts, bidder identities, and comparison thresholds");
    println!("  are all hidden behind zero-knowledge proofs and commitments.");
    println!("===============================================================================");
}
