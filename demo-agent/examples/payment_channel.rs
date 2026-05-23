//! Payment Channel Demo — Bounded-Counter Budget Channel Between Two Parties
//!
//! Demonstrates:
//! 1. Alice and Bob open a channel (shared cell with bounded counter budget)
//! 2. Alice sends payments to Bob by attenuating her slice of the budget
//! 3. Bob can verify each payment is valid without contacting the federation
//! 4. Channel closes with final balances settled via receipt chain
//! 5. Uses `coord/src/budget.rs` bounded counters (BudgetCoordinator struct)

use pyana_cell::CellId;
use pyana_coord::budget::BudgetCoordinator;
use pyana_turn::turn::TurnReceipt;
use pyana_turn::verify::verify_receipt_chain;

/// A payment from Alice to Bob within the channel.
/// Each payment attenuates Alice's remaining budget slice.
#[derive(Clone, Debug)]
struct ChannelPayment {
    /// Sequence number (monotonically increasing).
    seq: u64,
    /// Amount transferred in this payment.
    amount: u64,
    /// Running total sent by Alice.
    cumulative_sent: u64,
    /// Hash commitment to the payment (for receipt chain).
    digest: [u8; 32],
    /// Alice's remaining budget after this payment.
    alice_remaining: u64,
}

/// The channel state tracks cumulative flows.
#[derive(Clone, Debug)]
struct ChannelState {
    /// Alice's initial deposit (her budget slice ceiling).
    alice_deposit: u64,
    /// Total sent from Alice to Bob so far.
    total_sent: u64,
    /// All payments in order (the receipt chain).
    payments: Vec<ChannelPayment>,
}

impl ChannelState {
    fn alice_balance(&self) -> u64 {
        self.alice_deposit.saturating_sub(self.total_sent)
    }

    fn bob_balance(&self) -> u64 {
        self.total_sent
    }
}

/// Compute a debit digest for a payment.
fn payment_digest(seq: u64, amount: u64, sender: &[u8; 32]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-channel-payment-v1");
    hasher.update(&seq.to_le_bytes());
    hasher.update(&amount.to_le_bytes());
    hasher.update(sender);
    *hasher.finalize().as_bytes()
}

/// Build a receipt representing a channel state update.
fn make_channel_receipt(
    agent: CellId,
    channel_state: &ChannelState,
    previous: Option<&TurnReceipt>,
) -> TurnReceipt {
    // pre_state = hash of state before this update
    // post_state = hash of state after this update
    let pre_state = match previous {
        Some(prev) => prev.post_state_hash,
        None => [0u8; 32], // genesis
    };

    // Post-state commits to the current channel balances.
    let mut hasher = blake3::Hasher::new_derive_key("pyana-channel-state-v1");
    hasher.update(&channel_state.alice_balance().to_le_bytes());
    hasher.update(&channel_state.bob_balance().to_le_bytes());
    hasher.update(&channel_state.total_sent.to_le_bytes());
    let post_state = *hasher.finalize().as_bytes();

    let previous_receipt_hash = previous.map(|p| p.receipt_hash());

    TurnReceipt {
        turn_hash: [0u8; 32],
        forest_hash: [0u8; 32],
        pre_state_hash: pre_state,
        post_state_hash: post_state,
        timestamp: 1700000000 + channel_state.payments.len() as i64,
        effects_hash: [0u8; 32],
        computrons_used: 10,
        action_count: 1,
        previous_receipt_hash: previous_receipt_hash,
        agent,
        federation_id: [0u8; 32],
        routing_directives: Vec::new(),
        introduction_exports: Vec::new(),
        derivation_records: Vec::new(),
        emitted_events: Vec::new(),
        executor_signature: None,
        finality: Default::default(),
    }
}

fn main() {
    println!("=== Pyana Payment Channel Demo (Bounded-Counter Budget) ===\n");

    // --- Setup ---
    let alice_pubkey = blake3::derive_key("alice-channel-pubkey-v1", b"alice-channel-secret");
    let bob_pubkey = blake3::derive_key("bob-channel-pubkey-v1", b"bob-channel-secret");

    let alice_cell_id = CellId::derive_raw(&alice_pubkey, &[0u8; 32]);

    println!("Participants:");
    println!(
        "  Alice: {:02x}{:02x}{:02x}{:02x}... (sender)",
        alice_pubkey[0], alice_pubkey[1], alice_pubkey[2], alice_pubkey[3]
    );
    println!(
        "  Bob:   {:02x}{:02x}{:02x}{:02x}... (receiver)",
        bob_pubkey[0], bob_pubkey[1], bob_pubkey[2], bob_pubkey[3]
    );
    println!();

    // =======================================================================
    // STEP 1: OPEN CHANNEL — Create bounded counter budget
    // =======================================================================
    println!("--- Step 1: OPEN CHANNEL ---");

    // The channel is modeled as a BudgetCoordinator where:
    // - The "agent" is the channel cell
    // - "Silos" represent the two endpoints (Alice's side, Bob's side)
    // - Alice's silo gets a budget slice she can debit (send to Bob)
    // - The total balance is Alice's deposit
    let channel_deposit: u64 = 10000; // Alice deposits 10,000 units

    // We need 4 silos minimum for f=1 Byzantine tolerance.
    // Model: silo[0] = Alice endpoint, silo[1] = Bob endpoint,
    // silo[2] and silo[3] are watchtower witnesses.
    let alice_silo: [u8; 32] = {
        let mut s = [0u8; 32];
        s[0] = 0xAA;
        s
    };
    let bob_silo: [u8; 32] = {
        let mut s = [0u8; 32];
        s[0] = 0xBB;
        s
    };
    let witness_1: [u8; 32] = {
        let mut s = [0u8; 32];
        s[0] = 0xC1;
        s
    };
    let witness_2: [u8; 32] = {
        let mut s = [0u8; 32];
        s[0] = 0xC2;
        s
    };

    let silos = vec![alice_silo, bob_silo, witness_1, witness_2];
    let mut budget = BudgetCoordinator::new(
        alice_cell_id,
        channel_deposit,
        silos.clone(),
        1, // tolerate 1 Byzantine silo
    )
    .expect("Channel budget created");

    let slice_ceiling = budget.compute_slice_ceiling();

    println!("  Channel deposit: {} units", channel_deposit);
    println!("  Byzantine tolerance: f=1 (requires 4 silos: 2 endpoints + 2 witnesses)");
    println!(
        "  Slice ceiling per silo: {} units (balance * (f+1)/(2f+1) = {} * 2/3)",
        slice_ceiling, channel_deposit
    );
    println!(
        "  Alice's spending limit: {} units per epoch",
        slice_ceiling
    );
    println!();

    // =======================================================================
    // STEP 2: ALICE SENDS PAYMENTS TO BOB
    // =======================================================================
    println!("--- Step 2: ALICE SENDS PAYMENTS ---");
    println!("  Each payment debits Alice's budget slice (no federation contact needed).\n");

    let mut channel = ChannelState {
        alice_deposit: slice_ceiling, // Alice can spend up to her slice ceiling
        total_sent: 0,
        payments: Vec::new(),
    };

    let mut receipt_chain: Vec<TurnReceipt> = Vec::new();

    // Payment 1: Alice sends 1000 to Bob
    let payment_amounts = [1000u64, 2500, 500, 1500, 800];

    for (i, &amount) in payment_amounts.iter().enumerate() {
        let seq = i as u64 + 1;
        let digest = payment_digest(seq, amount, &alice_pubkey);

        // Debit from Alice's silo (the hot path: no coordination needed)
        let debit_result = budget.try_debit(alice_silo, amount, digest);

        match debit_result {
            Ok(()) => {
                channel.total_sent += amount;
                let remaining = budget.remaining(&alice_silo).unwrap();

                let payment = ChannelPayment {
                    seq,
                    amount,
                    cumulative_sent: channel.total_sent,
                    digest,
                    alice_remaining: remaining,
                };

                // Build receipt for this payment
                let prev = receipt_chain.last();
                let receipt = make_channel_receipt(alice_cell_id, &channel, prev);
                receipt_chain.push(receipt);
                channel.payments.push(payment.clone());

                println!("  Payment #{}: {} units -> Bob", seq, amount);
                println!(
                    "    Cumulative sent: {} | Alice remaining: {} | Bob accrued: {}",
                    payment.cumulative_sent,
                    payment.alice_remaining,
                    channel.bob_balance()
                );
            }
            Err(e) => {
                println!("  Payment #{}: REJECTED ({})", seq, e);
            }
        }
    }
    println!();

    // =======================================================================
    // STEP 3: BOB VERIFIES PAYMENTS OFFLINE
    // =======================================================================
    println!("--- Step 3: BOB VERIFIES PAYMENTS OFFLINE ---");
    println!("  Bob verifies the receipt chain without contacting the federation.\n");

    // Verify the receipt chain is valid
    let chain_result = verify_receipt_chain(&receipt_chain);
    assert!(chain_result.is_ok(), "Receipt chain should be valid");
    println!(
        "  Receipt chain valid: {} receipts linked [PASS]",
        receipt_chain.len()
    );

    // Bob checks monotonicity: cumulative_sent never decreases
    let mut prev_cumulative = 0u64;
    for payment in &channel.payments {
        assert!(
            payment.cumulative_sent >= prev_cumulative,
            "Cumulative sent must be monotonically increasing"
        );
        assert!(
            payment.cumulative_sent <= channel.alice_deposit,
            "Cumulative sent must not exceed channel deposit"
        );
        prev_cumulative = payment.cumulative_sent;
    }
    println!("  Monotonicity check: cumulative_sent never decreases [PASS]");
    println!(
        "  Bounds check: cumulative_sent <= slice ceiling ({}) [PASS]",
        channel.alice_deposit
    );

    // Bob can verify each payment's digest matches its claimed (seq, amount)
    for payment in &channel.payments {
        let expected_digest = payment_digest(payment.seq, payment.amount, &alice_pubkey);
        assert_eq!(payment.digest, expected_digest, "Payment digest must match");
    }
    println!(
        "  Digest integrity: all {} payment digests verified [PASS]",
        channel.payments.len()
    );
    println!();

    // =======================================================================
    // STEP 4: ATTEMPT OVERSPEND (budget enforcement)
    // =======================================================================
    println!("--- Step 4: BUDGET ENFORCEMENT ---");

    let remaining = budget.remaining(&alice_silo).unwrap();
    println!("  Alice's remaining budget: {} units", remaining);
    println!("  Attempting to overspend ({} units)...", remaining + 1);

    let overspend_digest = payment_digest(99, remaining + 1, &alice_pubkey);
    let overspend_result = budget.try_debit(alice_silo, remaining + 1, overspend_digest);
    assert!(overspend_result.is_err(), "Overspend should be rejected");

    match overspend_result {
        Err(ref e) => println!("  REJECTED: {} [PASS]", e),
        _ => unreachable!(),
    }
    println!();

    // =======================================================================
    // STEP 5: CLOSE CHANNEL — Settle via spending certificates
    // =======================================================================
    println!("--- Step 5: CLOSE CHANNEL (settlement) ---");

    // Alice's silo produces a spending certificate for the rebalance
    let alice_signing_key = *blake3::hash(&alice_silo).as_bytes();
    let alice_slice = budget.silo_states.get(&alice_silo).unwrap();
    let alice_cert = alice_slice.certificate(alice_silo, &alice_signing_key);

    println!("  Alice's spending certificate:");
    println!(
        "    Silo:        {:02x}{:02x}...",
        alice_silo[0], alice_silo[1]
    );
    println!("    Version:     {}", alice_cert.version);
    println!("    Total spent: {} units", alice_cert.total_spent);
    println!("    Debits:      {} transactions", alice_cert.debits.len());
    println!();

    // Bob's silo spent nothing (he only receives)
    let bob_signing_key = *blake3::hash(&bob_silo).as_bytes();
    let bob_slice = budget.silo_states.get(&bob_silo).unwrap();
    let bob_cert = bob_slice.certificate(bob_silo, &bob_signing_key);

    // Witnesses also spent nothing
    let w1_signing_key = *blake3::hash(&witness_1).as_bytes();
    let w1_slice = budget.silo_states.get(&witness_1).unwrap();
    let w1_cert = w1_slice.certificate(witness_1, &w1_signing_key);

    let w2_signing_key = *blake3::hash(&witness_2).as_bytes();
    let w2_slice = budget.silo_states.get(&witness_2).unwrap();
    let w2_cert = w2_slice.certificate(witness_2, &w2_signing_key);

    // Rebalance (settlement)
    let total_spent = budget
        .rebalance(&[alice_cert, bob_cert, w1_cert, w2_cert])
        .expect("Rebalance should succeed");

    println!("  Settlement complete!");
    println!("    Total spent in channel: {} units", total_spent);
    println!(
        "    Remaining balance (returned to Alice): {} units",
        budget.total_balance
    );
    println!(
        "    Bob receives: {} units (from {} payments)",
        channel.bob_balance(),
        channel.payments.len()
    );
    println!();

    // Verify conservation
    assert_eq!(
        total_spent + budget.total_balance,
        channel_deposit,
        "Conservation: spent + remaining = original deposit"
    );
    println!(
        "  Conservation: {} (spent) + {} (remaining) = {} (deposit) [PASS]",
        total_spent, budget.total_balance, channel_deposit
    );
    println!();

    // =======================================================================
    // STEP 6: FINAL STATE AND TRUST MODEL
    // =======================================================================
    println!("--- Step 6: FINAL STATE ---");
    println!("  ┌──────────────────────────────────────────────────────────┐");
    println!("  │ Channel Summary                                          │");
    println!("  ├──────────────────────────────────────────────────────────┤");
    println!(
        "  │ Original deposit:    {:>6} units                        │",
        channel_deposit
    );
    println!(
        "  │ Alice sent to Bob:   {:>6} units ({} payments)           │",
        channel.bob_balance(),
        channel.payments.len()
    );
    println!(
        "  │ Alice final balance: {:>6} units                        │",
        budget.total_balance
    );
    println!(
        "  │ Bob final balance:   {:>6} units                        │",
        channel.bob_balance()
    );
    println!(
        "  │ Budget version:      {:>6} (1 epoch completed)          │",
        budget.version
    );
    println!("  └──────────────────────────────────────────────────────────┘");
    println!();
    println!("  Trust model:");
    println!("  1. OFFLINE VERIFICATION: Bob verifies payments via receipt chain.");
    println!("     No federation contact needed for individual payments.");
    println!();
    println!(
        "  2. BOUNDED RISK: Alice can spend at most her slice ceiling ({}).",
        slice_ceiling
    );
    println!("     Even if she is malicious, overspend is bounded by (f+1)/(2f+1).");
    println!();
    println!("  3. ATOMICITY: Channel close is a single rebalance operation.");
    println!("     All spending certificates are verified against the budget.");
    println!();
    println!("  4. NO DOUBLE-SPEND: Each debit digest is unique. Replaying a");
    println!("     payment would require the same (seq, amount, sender) tuple.");
    println!();
    println!("=== Payment Channel Demo Complete ===");
}
