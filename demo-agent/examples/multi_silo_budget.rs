//! Multi-Silo Budget Demo — Bounded Counter Spending Without Consensus
//!
//! Demonstrates:
//! 1. An agent has a total budget of 1000 computrons
//! 2. Budget is split across 3 silos using Stingray bounded counters
//! 3. Each silo can spend locally up to its slice without coordination
//! 4. Parallel spending in all 3 silos (no locks, no consensus needed)
//! 5. Even if one silo is Byzantine, total spend cannot exceed the true balance
//! 6. Periodic rebalancing when one silo's slice is exhausted

use pyana_cell::CellId;
use pyana_coord::budget::BudgetCoordinator;

/// Helper: deterministic silo IDs for the demo.
fn silo_id(index: u8) -> [u8; 32] {
    let mut id = [0u8; 32];
    id[0] = index;
    id[31] = index.wrapping_mul(7); // slightly more distinctive
    id
}

/// Helper: deterministic debit digest from a transaction number.
fn debit_digest(tx_num: u64) -> [u8; 32] {
    *blake3::hash(&tx_num.to_le_bytes()).as_bytes()
}

fn main() {
    println!("=== Pyana Multi-Silo Budget Demo (Bounded Counters) ===\n");

    // ─── Setup ───────────────────────────────────────────────────────────────
    let agent = CellId::from_bytes([0xAA; 32]);
    let total_budget: u64 = 1000;

    // We need at least 3f+1 silos. For f=1 (tolerate 1 Byzantine silo), need 4.
    // We'll use 4 silos but highlight operations on 3 of them.
    let silo_a = silo_id(1);
    let silo_b = silo_id(2);
    let silo_c = silo_id(3);
    let silo_d = silo_id(4); // reserve silo (needed for 3f+1 = 4)

    let silos = vec![silo_a, silo_b, silo_c, silo_d];
    let byzantine_tolerance = 1; // tolerate 1 Byzantine silo

    println!("Agent:    {:02x}{:02x}{:02x}{:02x}...", agent.as_bytes()[0], agent.as_bytes()[1], agent.as_bytes()[2], agent.as_bytes()[3]);
    println!("Budget:   {} computrons", total_budget);
    println!("Silos:    {} (Byzantine tolerance f={})", silos.len(), byzantine_tolerance);
    println!("Required: 3f+1 = {} silos", 3 * byzantine_tolerance + 1);
    println!();

    // ─── Step 1: Initialize Budget Distribution ──────────────────────────────
    println!("--- Step 1: DISTRIBUTE BUDGET SLICES ---");

    let mut coord = BudgetCoordinator::new(agent, total_budget, silos.clone(), byzantine_tolerance)
        .expect("should have enough silos for f=1");

    let ceiling = coord.compute_slice_ceiling();
    println!("  Slice formula: ceiling = balance * (f+1) / (2f+1)");
    println!("  ceiling = {} * {} / {} = {}", total_budget, byzantine_tolerance + 1, 2 * byzantine_tolerance + 1, ceiling);
    println!();
    println!("  Per-silo budget slices (each silo can spend up to ceiling independently):");
    println!("    Silo A: ceiling = {}, spent = 0, remaining = {}", ceiling, ceiling);
    println!("    Silo B: ceiling = {}, spent = 0, remaining = {}", ceiling, ceiling);
    println!("    Silo C: ceiling = {}, spent = 0, remaining = {}", ceiling, ceiling);
    println!("    Silo D: ceiling = {}, spent = 0, remaining = {}", ceiling, ceiling);
    println!();
    println!("  Total allocated: {} (sum of all ceilings)", coord.total_allocated);
    println!("  NOTE: total_allocated ({}) > total_balance ({}) is expected!", coord.total_allocated, total_budget);
    println!("  The Stingray invariant guarantees correctness even with over-allocation.");
    println!();

    // ─── Step 2: Parallel Spending (No Coordination) ─────────────────────────
    println!("--- Step 2: PARALLEL SPENDING (NO LOCKS, NO CONSENSUS) ---");
    println!();

    // Each silo spends independently — simulating truly concurrent execution.
    // In a real system these would be on different machines with no communication.

    let mut tx_counter: u64 = 0;

    // Silo A: 3 debits totaling 200
    println!("  [Silo A] Spending locally (no coordination with B or C):");
    for amount in [80, 70, 50] {
        coord.try_debit(silo_a, amount, debit_digest(tx_counter)).unwrap();
        tx_counter += 1;
        println!("    debit {} computrons -> remaining: {}", amount, coord.remaining(&silo_a).unwrap());
    }
    println!();

    // Silo B: 2 debits totaling 300
    println!("  [Silo B] Spending locally (no coordination with A or C):");
    for amount in [150, 150] {
        coord.try_debit(silo_b, amount, debit_digest(tx_counter)).unwrap();
        tx_counter += 1;
        println!("    debit {} computrons -> remaining: {}", amount, coord.remaining(&silo_b).unwrap());
    }
    println!();

    // Silo C: 1 debit of 100
    println!("  [Silo C] Spending locally (no coordination with A or B):");
    coord.try_debit(silo_c, 100, debit_digest(tx_counter)).unwrap();
    tx_counter += 1;
    println!("    debit 100 computrons -> remaining: {}", coord.remaining(&silo_c).unwrap());
    println!();

    println!("  Summary after parallel spending:");
    println!("    Silo A: spent 200, remaining {}", coord.remaining(&silo_a).unwrap());
    println!("    Silo B: spent 300, remaining {}", coord.remaining(&silo_b).unwrap());
    println!("    Silo C: spent 100, remaining {}", coord.remaining(&silo_c).unwrap());
    println!("    Silo D: spent 0,   remaining {}", coord.remaining(&silo_d).unwrap());
    println!("    Total spent across all silos: {}", coord.total_spent());
    println!();
    println!("  KEY POINT: All 6 debits required ZERO coordination between silos!");
    println!("  Each silo checked only its local slice — no locks, no consensus round.");
    println!();

    // ─── Step 3: Slice Exhaustion ────────────────────────────────────────────
    println!("--- Step 3: SLICE EXHAUSTION ---");
    println!();

    // Demonstrate what happens when a silo tries to exceed its ceiling.
    let remaining_a = coord.remaining(&silo_a).unwrap();
    println!("  Silo A remaining: {}", remaining_a);
    println!("  Attempting to spend {} (more than remaining)...", remaining_a + 1);
    let err = coord.try_debit(silo_a, remaining_a + 1, debit_digest(tx_counter)).unwrap_err();
    tx_counter += 1;
    println!("  REJECTED: {}", err);
    println!();
    println!("  The silo cannot exceed its ceiling — not even by 1 computron.");
    println!("  It must wait for a rebalance to get a fresh slice.");
    println!();

    // ─── Step 4: Rebalancing ─────────────────────────────────────────────────
    println!("--- Step 4: REBALANCING (Periodic Coordination) ---");
    println!();
    println!("  Collecting spending certificates from all silos...");

    // Collect certificates from all silos (Silo D spent nothing this epoch).
    let cert_a = coord.silo_states[&silo_a].certificate(silo_a);
    let cert_b = coord.silo_states[&silo_b].certificate(silo_b);
    let cert_c = coord.silo_states[&silo_c].certificate(silo_c);
    let cert_d = coord.silo_states[&silo_d].certificate(silo_d);

    println!("    Silo A certificate: spent {} ({} debits)", cert_a.total_spent, cert_a.debits.len());
    println!("    Silo B certificate: spent {} ({} debits)", cert_b.total_spent, cert_b.debits.len());
    println!("    Silo C certificate: spent {} ({} debits)", cert_c.total_spent, cert_c.debits.len());
    println!("    Silo D certificate: spent {} ({} debits)", cert_d.total_spent, cert_d.debits.len());
    println!();

    let old_balance = coord.total_balance;
    let old_version = coord.version;

    let total_epoch_spent = coord
        .rebalance(&[cert_a, cert_b, cert_c, cert_d])
        .expect("rebalance should succeed with valid certificates");

    println!("  Rebalance complete!");
    println!("    Total spent this epoch: {}", total_epoch_spent);
    println!("    Balance before: {}", old_balance);
    println!("    Balance after:  {}", coord.total_balance);
    println!("    Budget version: {} -> {}", old_version, coord.version);
    println!();

    let new_ceiling = coord.compute_slice_ceiling();
    println!("  New slice distribution (budget version {}):", coord.version);
    println!("    New ceiling: {} * {} / {} = {}", coord.total_balance, byzantine_tolerance + 1, 2 * byzantine_tolerance + 1, new_ceiling);
    println!("    Silo A: ceiling = {}, remaining = {}", new_ceiling, coord.remaining(&silo_a).unwrap());
    println!("    Silo B: ceiling = {}, remaining = {}", new_ceiling, coord.remaining(&silo_b).unwrap());
    println!("    Silo C: ceiling = {}, remaining = {}", new_ceiling, coord.remaining(&silo_c).unwrap());
    println!("    Silo D: ceiling = {}, remaining = {}", new_ceiling, coord.remaining(&silo_d).unwrap());
    println!();

    // ─── Step 5: Post-Rebalance Spending ─────────────────────────────────────
    println!("--- Step 5: POST-REBALANCE SPENDING ---");
    println!();
    println!("  Silo A can now spend again from its fresh slice!");

    coord.try_debit(silo_a, 50, debit_digest(tx_counter)).unwrap();
    tx_counter += 1;
    println!("    Silo A: debit 50 -> remaining {}", coord.remaining(&silo_a).unwrap());

    coord.try_debit(silo_b, 30, debit_digest(tx_counter)).unwrap();
    println!("    Silo B: debit 30 -> remaining {}", coord.remaining(&silo_b).unwrap());
    println!();

    // ─── Step 6: Byzantine Safety Guarantee ──────────────────────────────────
    println!("--- Step 6: BYZANTINE SAFETY ---");
    println!();
    println!("  Demonstrating with a separate budget coordinator that a Byzantine");
    println!("  silo's damage is bounded by its ceiling...");
    println!();

    // Use a separate coordinator to demonstrate Byzantine behavior in isolation.
    let mut byz_coord = BudgetCoordinator::new(agent, total_budget, silos.clone(), byzantine_tolerance)
        .unwrap();
    let byz_ceiling = byz_coord.compute_slice_ceiling();

    // Byzantine silo spends everything it can
    let mut byzantine_spent = 0u64;
    let mut byz_tx: u64 = 1000;
    loop {
        let result = byz_coord.try_debit(silo_d, 100, debit_digest(byz_tx));
        byz_tx += 1;
        match result {
            Ok(()) => byzantine_spent += 100,
            Err(_) => break,
        }
    }
    // Spend the remainder
    let byz_remainder = byz_coord.remaining(&silo_d).unwrap();
    if byz_remainder > 0 {
        byz_coord.try_debit(silo_d, byz_remainder, debit_digest(byz_tx)).unwrap();
        byzantine_spent += byz_remainder;
    }

    println!("  Byzantine Silo D spent its full ceiling: {} computrons", byzantine_spent);
    assert_eq!(byzantine_spent, byz_ceiling);
    println!("  Ceiling was: {} -- the silo CANNOT spend more than this.", byz_ceiling);
    println!();
    println!("  Even if the Byzantine silo lies about its spending, the protocol");
    println!("  guarantees:");
    println!("    - Its certificate cannot claim more than the ceiling");
    println!("    - Honest silos independently track their own spending");
    println!("    - Total confirmed spend is bounded by: balance + f * ceiling");
    println!("      = {} + {} * {} = {}", total_budget, byzantine_tolerance, byz_ceiling, total_budget + (byzantine_tolerance as u64) * byz_ceiling);
    println!();
    println!("  In the worst case, the overspend ({}) is bounded and recoverable.", byz_ceiling);
    println!("  No Byzantine silo can drain the entire system's balance.");
    println!();

    // ─── Summary ─────────────────────────────────────────────────────────────
    println!("--- PROTOCOL PROPERTIES ---");
    println!();
    println!("  1. LOCAL FAST PATH: Each silo debits from its local slice with zero");
    println!("     coordination. This is the common case for agent execution metering.");
    println!();
    println!("  2. BOUNDED OVERSPEND: Even with f={} Byzantine silos, the maximum", byzantine_tolerance);
    println!("     unconfirmed spend is bounded by the ceiling formula:");
    println!("     ceiling = balance * (f+1) / (2f+1)");
    println!();
    println!("  3. PERIODIC RECONCILIATION: Rebalancing collects spending certificates,");
    println!("     deducts true spend from the agent's balance, and issues fresh slices.");
    println!();
    println!("  4. NO GLOBAL LOCKS: Unlike a centralized rate limiter, silos never");
    println!("     block each other. Exhausted silos just wait for the next rebalance.");
    println!();
    println!("  5. BYZANTINE FAULT TOLERANT: A malicious silo cannot spend more than");
    println!("     its ceiling. The protocol detects and bounds overspend at rebalance.");
    println!();
    println!("=== Multi-Silo Budget Demo Complete ===");
}
