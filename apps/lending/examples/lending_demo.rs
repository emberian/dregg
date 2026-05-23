//! Lending protocol demonstration: supply, borrow, accrue, repay, liquidate.
//!
//! This example walks through the full lifecycle of a lending position using
//! pyana's obligation and temporal predicate primitives, with real STARK proofs.

use pyana_lending::borrow::CollateralEntry;
use pyana_lending::circuit::{
    HealthFactorDescriptor, HealthFactorWitness, InterestAccrualDescriptor, InterestAccrualWitness,
    RATE_PRECISION, prove_health_factor, prove_interest_accrual, verify_health_factor_proof,
    verify_interest_accrual_proof,
};
use pyana_lending::interest::{BLOCKS_PER_YEAR, BPS_SCALE};
use pyana_lending::liquidation::LiquidationResult;
use pyana_lending::{LendingPool, Market};
use pyana_types::CellId;

fn main() {
    println!("=== Pyana Lending Protocol Demo ===\n");

    let alice = CellId([0xAA; 32]); // Supplier
    let bob = CellId([0xBB; 32]); // Borrower
    let charlie = CellId([0xCC; 32]); // Liquidator

    // --- Setup ---
    let mut pool = LendingPool::new();
    pool.add_market(Market::new(1)); // Stablecoin
    pool.add_market(Market::new(2)); // Volatile asset
    println!("[Setup] Created lending pool with 2 markets (stablecoin=1, volatile=2)");

    // --- 1. Supply ---
    let supply_receipt = pool.supply(alice, 1, 10_000_000).unwrap();
    println!(
        "\n[Supply] Alice deposits 10,000,000 stablecoins -> receipt for position {:02x}{:02x}...",
        supply_receipt.position_id[0], supply_receipt.position_id[1]
    );
    println!(
        "  Market utilization: {}%",
        pool.get_market(1).unwrap().utilization_bps() as f64 / 100.0
    );

    // --- 2. Borrow ---
    let collateral = vec![CollateralEntry {
        asset_id: 2,
        amount: 8_000_000,
        price: BPS_SCALE, // 1:1 initially
    }];
    let borrow_id = pool.borrow(bob, 1, 5_000_000, collateral).unwrap();
    println!("\n[Borrow] Bob borrows 5,000,000 stablecoins against 8,000,000 volatile collateral");
    let pos = pool
        .borrow_positions
        .iter()
        .find(|p| p.id == borrow_id)
        .unwrap();
    println!(
        "  Health factor: {:.2} (threshold: 1.0)",
        pos.health_factor_bps() as f64 / BPS_SCALE as f64
    );
    println!(
        "  Market utilization: {}%",
        pool.get_market(1).unwrap().utilization_bps() as f64 / 100.0
    );

    // --- 3. Interest Accrual ---
    let blocks = BLOCKS_PER_YEAR / 4; // 3 months
    pool.advance_to_block(blocks);
    println!("\n[Accrue] Advanced {} blocks (3 months)", blocks);
    let market = pool.get_market(1).unwrap();
    println!("  Total borrows: {} (was 5,000,000)", market.total_borrows);
    println!(
        "  Supply APY: {:.2}%",
        market.supply_apy_bps() as f64 / 100.0
    );
    println!(
        "  Borrow APY: {:.2}%",
        market.borrow_apy_bps() as f64 / 100.0
    );
    let alice_value = supply_receipt.current_value(market.borrow_index);
    println!(
        "  Alice's supply value: {} (earned {} interest)",
        alice_value,
        alice_value - 10_000_000
    );

    // --- 4. STARK Circuit Proofs ---
    println!("\n[Circuit] Generating STARK proof of health factor...");
    let health_witness = HealthFactorWitness {
        collateral_amounts: vec![8_000_000],
        collateral_prices: vec![BPS_SCALE],
        debt_amount: 5_000_000,
        threshold_bps: 8_000,
    };
    assert!(health_witness.is_healthy());
    match prove_health_factor(&health_witness) {
        Ok(proof_bytes) => {
            println!("  STARK proof generated ({} bytes)", proof_bytes.len());
            match verify_health_factor_proof(&proof_bytes, &health_witness) {
                Ok(()) => println!("  STARK proof verified successfully!"),
                Err(e) => println!("  Verification failed: {}", e),
            }
        }
        Err(e) => println!("  Proof generation failed: {}", e),
    }

    println!("\n[Circuit] Generating STARK proof of interest accrual...");
    let accrual_witness = InterestAccrualWitness {
        start_balance: 5_000_000,
        rate_per_block: RATE_PRECISION / 10_000, // 0.01% per block
        num_blocks: 8,                           // power of two for clean trace
    };
    let end_balance = accrual_witness.compute_end_balance();
    println!(
        "  After {} blocks at 0.01%%/block: {} -> {}",
        accrual_witness.num_blocks, 5_000_000, end_balance
    );
    match prove_interest_accrual(&accrual_witness) {
        Ok(proof_bytes) => {
            println!("  STARK proof generated ({} bytes)", proof_bytes.len());
            match verify_interest_accrual_proof(&proof_bytes, &accrual_witness) {
                Ok(()) => println!("  STARK proof verified successfully!"),
                Err(e) => println!("  Verification failed: {}", e),
            }
        }
        Err(e) => println!("  Proof generation failed: {}", e),
    }

    // --- 5. Descriptor-based proofs ---
    println!("\n[Circuit] Using descriptor API for health factor...");
    let health_desc = HealthFactorDescriptor {
        collateral_amounts: vec![8_000_000],
        collateral_prices: vec![BPS_SCALE],
        debt_amount: 5_000_000,
        threshold_bps: 8_000,
    };
    println!("  Position healthy: {}", health_desc.is_healthy());
    match health_desc.prove() {
        Ok(proof) => {
            println!("  Proof generated ({} bytes)", proof.len());
            match health_desc.verify(&proof) {
                Ok(()) => println!("  Proof verified!"),
                Err(e) => println!("  Verify failed: {}", e),
            }
        }
        Err(e) => println!("  Prove failed: {}", e),
    }

    let accrual_desc = InterestAccrualDescriptor {
        start_balance: 5_000_000,
        rate_per_block: RATE_PRECISION / 10_000,
        num_blocks: 8,
        expected_end_balance: 0,
    };
    let computed_end = accrual_desc.compute_end_balance();
    let valid_desc = InterestAccrualDescriptor {
        expected_end_balance: computed_end,
        ..accrual_desc
    };
    println!("\n[Circuit] Using descriptor API for interest accrual...");
    match valid_desc.prove() {
        Ok(proof) => {
            println!("  Proof generated ({} bytes)", proof.len());
            match valid_desc.verify_proof(&proof) {
                Ok(()) => println!("  Proof verified!"),
                Err(e) => println!("  Verify failed: {}", e),
            }
        }
        Err(e) => println!("  Prove failed: {}", e),
    }

    // --- 6. Repay ---
    let pos = pool
        .borrow_positions
        .iter()
        .find(|p| p.id == borrow_id)
        .unwrap();
    let total_owed = pos.total_debt();
    let repaid = pool.repay(&borrow_id, total_owed).unwrap();
    println!("\n[Repay] Bob repays {} (principal + interest)", repaid);
    let pos = pool
        .borrow_positions
        .iter()
        .find(|p| p.id == borrow_id)
        .unwrap();
    println!("  Position repaid: {}", pos.repaid);

    // --- 7. Liquidation Demo ---
    println!("\n[Liquidation] Demonstrating liquidation scenario...");

    // Create a new risky position
    let risky_collateral = vec![CollateralEntry {
        asset_id: 2,
        amount: 1_300_000,
        // Price crash: collateral worth only 75% of par
        price: BPS_SCALE * 75 / 100,
    }];
    let risky_id = pool.borrow(bob, 1, 1_000_000, risky_collateral).unwrap();
    let pos = pool
        .borrow_positions
        .iter()
        .find(|p| p.id == risky_id)
        .unwrap();
    println!(
        "  Risky position health: {:.2}",
        pos.health_factor_bps() as f64 / BPS_SCALE as f64
    );

    if !pos.is_healthy() {
        let result = pool.liquidate(&risky_id, charlie, 400_000, 2).unwrap();
        match result {
            LiquidationResult::Success(receipt) => {
                println!("  Liquidation SUCCESS!");
                println!("    Debt repaid: {}", receipt.debt_repaid);
                println!("    Collateral seized: {:?}", receipt.collateral_seized);
                println!("    Liquidator bonus: {}", receipt.bonus_amount);
            }
            other => println!("  Liquidation result: {:?}", other),
        }
    } else {
        println!("  Position is healthy, no liquidation needed");
    }

    // --- 8. Withdraw ---
    let market = pool.get_market(1).unwrap();
    let final_value = supply_receipt.current_value(market.borrow_index);
    println!("\n[Withdraw] Alice's final supply value: {}", final_value);
    println!(
        "  Total interest earned: {} ({:.2}%)",
        final_value - 10_000_000,
        (final_value - 10_000_000) as f64 / 10_000_000.0 * 100.0
    );

    println!("\n=== Demo Complete ===");
}
