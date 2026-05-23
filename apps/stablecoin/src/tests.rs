//! Integration tests for the CDP stablecoin system.
//!
//! These tests exercise the full lifecycle including circuit proof generation
//! and verification, position management, and liquidation scenarios.

use pyana_cell::CellId;
use pyana_circuit::field::BabyBear;
use pyana_dsl_runtime::ProgramRegistry;

use crate::cdp::{
    CollateralPosition, ETH_ASSET_TYPE, PUSD_ASSET_TYPE, PositionStatus, StablecoinRegistry,
};
use crate::circuit::{self, CdpWitness, MIN_RATIO_BPS};
use crate::liquidation::LiquidationEngine;
use crate::oracle::{PriceOracle, test_attestation, test_oracle_pubkey};

const ORACLE_KEY: [u8; 32] = [0x01; 32];

fn setup_oracle() -> PriceOracle {
    let pubkey = test_oracle_pubkey(&ORACLE_KEY);
    PriceOracle::new(vec![pubkey], 100)
}

fn alice() -> CellId {
    CellId([0xAA; 32])
}

fn bob() -> CellId {
    CellId([0xBB; 32])
}

// =============================================================================
// Full Lifecycle Test
// =============================================================================

#[test]
fn full_cdp_lifecycle() {
    let mut registry = StablecoinRegistry::new();
    let mut oracle = setup_oracle();

    // 1. Oracle submits initial price: ETH = $2000
    let attestation = test_attestation("ETH/USD", 2000, 50, ORACLE_KEY);
    oracle.submit_attestation(attestation.clone(), 55).unwrap();

    // 2. Alice opens a CDP with 100 ETH
    let mut position =
        CollateralPosition::open(alice(), 100, ETH_ASSET_TYPE, MIN_RATIO_BPS, 100).unwrap();
    registry.register(position.clone());

    // 3. Alice mints 100,000 PUSD (well within 150% ratio)
    // collateral_value = 100 * 2000 = 200,000
    // debt_threshold = 100,000 * 15000 = 1,500,000,000
    // scaled_collateral = 200,000 * 10000 = 2,000,000,000
    // 2,000,000,000 >= 1,500,000,000 => healthy
    let transition = position.mint(100_000, &attestation, 55, 100).unwrap();
    registry.update(&position);
    registry.record_mint(100_000);

    assert_eq!(position.debt_amount, 100_000);
    assert_eq!(registry.total_supply, 100_000);
    assert!(!transition.proof.is_empty());

    // Verify the proof
    let witness = CdpWitness {
        collateral_amount: 100,
        price: 2000,
        debt_amount: 100_000,
        ratio_bps: MIN_RATIO_BPS,
        position_id: position.id,
        oracle_commitment: attestation.commitment(),
        price_timestamp: 50,
        max_age: 100,
    };
    let verify_result = circuit::verify_cdp_ratio(&transition.proof, &witness);
    assert!(
        verify_result.is_ok(),
        "Proof verification failed: {:?}",
        verify_result.err()
    );

    // 4. Alice repays 50,000 PUSD
    let transition = position.repay(50_000, &attestation, 100).unwrap();
    registry.update(&position);
    registry.record_burn(50_000);

    assert_eq!(position.debt_amount, 50_000);
    assert_eq!(registry.total_supply, 50_000);
    assert!(!transition.proof.is_empty());

    // 5. Alice repays remaining 50,000 and closes
    position.repay(50_000, &attestation, 100).unwrap();
    registry.update(&position);
    registry.record_burn(50_000);

    assert_eq!(position.debt_amount, 0);
    assert_eq!(registry.total_supply, 0);

    let transition = position.close().unwrap();
    registry.update(&transition.position);
    assert_eq!(transition.position.status, PositionStatus::Closed);
}

// =============================================================================
// Liquidation Test
// =============================================================================

#[test]
fn price_drop_triggers_liquidation() {
    let mut registry = StablecoinRegistry::new();
    let engine = LiquidationEngine::default_config();

    // Alice opens CDP: 100 ETH at $2000, mints 100,000 PUSD
    let attestation_high = test_attestation("ETH/USD", 2000, 50, ORACLE_KEY);
    let mut position =
        CollateralPosition::open(alice(), 100, ETH_ASSET_TYPE, MIN_RATIO_BPS, 100).unwrap();
    position.mint(100_000, &attestation_high, 55, 100).unwrap();
    registry.register(position.clone());
    registry.record_mint(100_000);

    // Price was $2000, ratio was 200%. Now price drops to $1200.
    // New ratio: 100 * 1200 * 10000 / 100_000 = 12000 bps = 120% < 150%
    let new_price = 1200;
    assert!(position.is_liquidatable(new_price));

    // Bob liquidates Alice's position
    let liquidatable = engine.scan_liquidatable(&registry, ETH_ASSET_TYPE, new_price);
    assert_eq!(liquidatable.len(), 1);
    assert_eq!(liquidatable[0].id, position.id);

    let result = engine
        .liquidate(&mut position, bob(), new_price, 200)
        .unwrap();
    registry.update(&position);
    registry.record_burn(result.debt_repaid);

    assert_eq!(result.debt_repaid, 100_000);
    // Seizure: 100_000 * 10500 / (1200 * 10000) = 1_050_000_000 / 12_000_000 = 87
    assert_eq!(result.collateral_seized, 87);
    assert_eq!(result.collateral_returned, 13); // 100 - 87 = 13 returned to Alice
    assert_eq!(
        position.status,
        PositionStatus::Liquidated {
            liquidated_at: 200,
            liquidator: bob(),
        }
    );
    assert_eq!(registry.total_supply, 0);
}

// =============================================================================
// Circuit Deploy and Verify via Registry
// =============================================================================

#[test]
fn cdp_program_deploys_and_verifies() {
    let mut registry = ProgramRegistry::new();
    let vk_hash = circuit::deploy_cdp_program(&mut registry).unwrap();
    assert!(registry.contains(&vk_hash));

    // Generate a valid proof
    let witness = CdpWitness {
        collateral_amount: 500,
        price: 100,
        debt_amount: 20_000,
        ratio_bps: MIN_RATIO_BPS,
        position_id: [0xDE; 32],
        oracle_commitment: BabyBear::new(42),
        price_timestamp: 100,
        max_age: 50,
    };
    assert!(witness.is_healthy());

    let public_inputs = witness.public_inputs();
    let program = circuit::cdp_cell_program();
    let num_rows = 2;
    let witness_map = witness.to_witness_map(num_rows);
    let proof_bytes = program
        .prove_transition(&witness_map, num_rows, &public_inputs)
        .unwrap();

    // Verify via registry
    let result = registry.verify_with_program(&vk_hash, &public_inputs, &proof_bytes);
    assert!(
        result.is_ok(),
        "Registry verification failed: {:?}",
        result.err()
    );
}

// =============================================================================
// Oracle Price Update Triggers Liquidation Threshold
// =============================================================================

#[test]
fn oracle_update_triggers_liquidation_threshold() {
    let mut oracle = setup_oracle();
    let engine = LiquidationEngine::default_config();

    // Start with high price
    let high_price = test_attestation("ETH/USD", 3000, 10, ORACLE_KEY);
    oracle.submit_attestation(high_price.clone(), 15).unwrap();

    // Open position at high price
    let mut position =
        CollateralPosition::open(alice(), 100, ETH_ASSET_TYPE, MIN_RATIO_BPS, 50).unwrap();
    position.mint(150_000, &high_price, 15, 100).unwrap();
    // Ratio: 100*3000*10000 / 150_000 = 20000 bps = 200% (healthy)

    assert!(!position.is_liquidatable(3000));
    assert!(!position.is_liquidatable(2250)); // 100*2250*10000/150_000 = 15000 (exactly at threshold)

    // Price drops to 2000 => ratio = 100*2000*10000/150_000 = 13333 bps = 133% (liquidatable!)
    let low_price = test_attestation("ETH/USD", 2000, 60, ORACLE_KEY);
    oracle.submit_attestation(low_price.clone(), 65).unwrap();

    assert!(position.is_liquidatable(2000));

    // Execute liquidation
    let result = engine.liquidate(&mut position, bob(), 2000, 70).unwrap();
    assert_eq!(result.debt_repaid, 150_000);
    assert_eq!(position.debt_amount, 0);
}

// =============================================================================
// Multiple Positions with Different Health Levels
// =============================================================================

#[test]
fn selective_liquidation_only_unhealthy() {
    let engine = LiquidationEngine::default_config();
    let mut registry = StablecoinRegistry::new();

    // Position 1: heavily collateralized (300%)
    let attestation = test_attestation("ETH/USD", 3000, 50, ORACLE_KEY);
    let mut p1 =
        CollateralPosition::open(alice(), 1000, ETH_ASSET_TYPE, MIN_RATIO_BPS, 100).unwrap();
    p1.mint(1_000_000, &attestation, 55, 100).unwrap();
    // Ratio: 1000*3000*10000/1_000_000 = 30000 bps = 300%
    registry.register(p1.clone());

    // Position 2: barely collateralized (160%)
    let mut p2 = CollateralPosition::open(bob(), 800, ETH_ASSET_TYPE, MIN_RATIO_BPS, 100).unwrap();
    p2.debt_amount = 1_000_000; // manually set for test
    // Ratio: 800*3000*10000/1_000_000 = 24000 bps = 240%
    registry.register(p2.clone());

    // At price=3000, neither is liquidatable
    let liq = engine.scan_liquidatable(&registry, ETH_ASSET_TYPE, 3000);
    assert_eq!(liq.len(), 0);

    // Price drops to 1500:
    // p1: 1000*1500*10000/1_000_000 = 15000 bps = 150% (exactly at threshold, NOT liquidatable)
    // p2: 800*1500*10000/1_000_000 = 12000 bps = 120% (LIQUIDATABLE)
    let liq = engine.scan_liquidatable(&registry, ETH_ASSET_TYPE, 1500);
    assert_eq!(liq.len(), 1);
    assert_eq!(liq[0].id, p2.id);

    // Price drops to 1000:
    // p1: 1000*1000*10000/1_000_000 = 10000 bps = 100% (LIQUIDATABLE)
    // p2: 800*1000*10000/1_000_000 = 8000 bps = 80% (LIQUIDATABLE)
    let liq = engine.scan_liquidatable(&registry, ETH_ASSET_TYPE, 1000);
    assert_eq!(liq.len(), 2);
}

// =============================================================================
// Proof Soundness: Cannot Prove Under-Collateralized Position
// =============================================================================

#[test]
fn under_collateralized_witness_fails_health_check() {
    let witness = CdpWitness {
        collateral_amount: 10,
        price: 100,
        debt_amount: 1_000_000,
        ratio_bps: MIN_RATIO_BPS,
        position_id: [0xFF; 32],
        oracle_commitment: BabyBear::new(1),
        price_timestamp: 100,
        max_age: 50,
    };
    // 10 * 100 * 10000 = 10_000_000
    // 1_000_000 * 15000 = 15_000_000_000
    // 10_000_000 < 15_000_000_000 => unhealthy
    assert!(!witness.is_healthy());
}

// =============================================================================
// Note Asset Type Consistency
// =============================================================================

#[test]
fn minted_notes_have_correct_asset_type() {
    let attestation = test_attestation("ETH/USD", 2000, 50, ORACLE_KEY);
    let mut position =
        CollateralPosition::open(alice(), 100, ETH_ASSET_TYPE, MIN_RATIO_BPS, 100).unwrap();

    let transition = position.mint(50_000, &attestation, 55, 100).unwrap();

    assert_eq!(transition.created_notes.len(), 1);
    let note = &transition.created_notes[0];
    assert_eq!(note.fields[0], PUSD_ASSET_TYPE);
    assert_eq!(note.fields[1], 50_000);
    assert_eq!(note.owner, alice().0);
}

// =============================================================================
// Total Value Locked
// =============================================================================

#[test]
fn total_value_locked_calculation() {
    let mut registry = StablecoinRegistry::new();

    let p1 = CollateralPosition::open(alice(), 500, ETH_ASSET_TYPE, MIN_RATIO_BPS, 100).unwrap();
    let p2 = CollateralPosition::open(bob(), 300, ETH_ASSET_TYPE, MIN_RATIO_BPS, 101).unwrap();

    registry.register(p1);
    registry.register(p2);

    // TVL at price 2000: (500 + 300) * 2000 = 1,600,000
    assert_eq!(registry.total_value_locked(ETH_ASSET_TYPE, 2000), 1_600_000);
}
