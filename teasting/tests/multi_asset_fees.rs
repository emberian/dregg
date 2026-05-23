//! Multi-asset fee scenarios in multi-node simulation context.
//!
//! Exercises computron payments, USDC at configured rate, stale exchange rate
//! rejection, strict mode enforcement, and meta-transaction solver pattern.

use pyana_storage::multi_asset::{COMPUTRON_ASSET, ExchangeRate, FeeError, FeePayment, FeePolicy};
use pyana_teasting::harness::SimulationHarness;

/// Deterministic asset ID from a name.
fn asset_id(name: &str) -> [u8; 32] {
    *blake3::hash(name.as_bytes()).as_bytes()
}

/// USDC asset identifier.
fn usdc() -> [u8; 32] {
    asset_id("USDC")
}

/// ETH asset identifier.
fn eth() -> [u8; 32] {
    asset_id("ETH")
}

/// A custom token.
fn custom_token() -> [u8; 32] {
    asset_id("MY_TOKEN")
}

// ---------------------------------------------------------------------------
// Test 1: Service accepts computrons (default) -> payment works
// ---------------------------------------------------------------------------
#[test]
fn computron_default_payment_works() {
    let mut harness = SimulationHarness::new_federation(3);
    harness.advance_blocks(10);

    let policy = FeePolicy::computrons_only();

    // Valid computron payment.
    let payment = FeePayment {
        asset: COMPUTRON_ASSET,
        amount: 5000,
        computron_equivalent: 5000, // 1:1 rate
    };

    let result = policy.validate_payment(&payment, harness.clock.block_height);
    assert_eq!(result, Ok(5000));

    // Computron rate never stales (max_age = u64::MAX).
    harness.advance_blocks(1_000_000);
    let result = policy.validate_payment(&payment, harness.clock.block_height);
    assert_eq!(result, Ok(5000));
}

// ---------------------------------------------------------------------------
// Test 2: Service accepts USDC at configured rate -> payment in USDC works
// ---------------------------------------------------------------------------
#[test]
fn usdc_at_configured_rate_accepted() {
    let mut harness = SimulationHarness::new_federation(3);
    harness.advance_blocks(50);

    // 1 USDC = 100 computrons, rate valid for 200 blocks from height 50.
    let policy = FeePolicy::multi_asset(vec![(
        usdc(),
        ExchangeRate {
            rate: 100,
            updated_at: harness.clock.block_height,
            max_age: 200,
        },
    )]);

    // Pay 10 USDC = 1000 computrons.
    let payment = FeePayment {
        asset: usdc(),
        amount: 10,
        computron_equivalent: 1000,
    };

    harness.advance_blocks(50); // height 100, rate still fresh (50 + 200 = 250 > 100)
    let result = policy.validate_payment(&payment, harness.clock.block_height);
    assert_eq!(result, Ok(1000));

    // Also test the to_computrons helper.
    let equivalent = policy.to_computrons(&usdc(), 25, harness.clock.block_height);
    assert_eq!(equivalent, Ok(2500)); // 25 * 100
}

// ---------------------------------------------------------------------------
// Test 3: Stale exchange rate -> payment rejected
// ---------------------------------------------------------------------------
#[test]
fn stale_exchange_rate_rejects_payment() {
    let mut harness = SimulationHarness::new_federation(3);
    harness.advance_blocks(10);

    // Rate updated at height 10, max_age = 50.
    let policy = FeePolicy::multi_asset(vec![(
        usdc(),
        ExchangeRate {
            rate: 100,
            updated_at: 10,
            max_age: 50,
        },
    )]);

    let payment = FeePayment {
        asset: usdc(),
        amount: 5,
        computron_equivalent: 500,
    };

    // At height 60 (10 + 50 = 60), rate is still valid (not stale yet).
    let result = policy.validate_payment(&payment, 60);
    assert_eq!(result, Ok(500));

    // At height 61 (> 10 + 50), rate is stale.
    let result = policy.validate_payment(&payment, 61);
    assert!(matches!(
        result,
        Err(FeeError::StaleRate {
            asset: _,
            updated_at: 10,
            current_height: 61,
            max_age: 50,
        })
    ));
}

// ---------------------------------------------------------------------------
// Test 4: Strict mode: unlisted asset rejected
// ---------------------------------------------------------------------------
#[test]
fn strict_mode_rejects_unlisted_asset() {
    let mut harness = SimulationHarness::new_federation(3);
    harness.advance_blocks(5);

    // Policy only accepts USDC in strict mode.
    let mut policy = FeePolicy::multi_asset(vec![(
        usdc(),
        ExchangeRate {
            rate: 100,
            updated_at: 0,
            max_age: 10_000,
        },
    )]);
    policy.set_strict(true);

    // USDC accepted.
    assert!(policy.accepts(&usdc()));

    // ETH not in the list -> rejected.
    assert!(!policy.accepts(&eth()));
    let payment = FeePayment {
        asset: eth(),
        amount: 1,
        computron_equivalent: 5000,
    };
    let result = policy.validate_payment(&payment, harness.clock.block_height);
    assert!(matches!(result, Err(FeeError::AssetNotAccepted { .. })));

    // Custom token also rejected.
    assert!(!policy.accepts(&custom_token()));
}

// ---------------------------------------------------------------------------
// Test 5: Meta-transaction: solver fronts computrons, accepts user's token
// ---------------------------------------------------------------------------
#[test]
fn meta_transaction_solver_pattern() {
    let mut harness = SimulationHarness::new_federation(3);
    harness.advance_blocks(100);

    // Scenario: user holds MY_TOKEN, service only accepts computrons.
    // A solver accepts MY_TOKEN from user and pays computrons to the service.

    // Service policy: computrons only.
    let service_policy = FeePolicy::computrons_only();

    // Solver's acceptance policy: accepts MY_TOKEN at rate 50.
    let solver_policy = FeePolicy::multi_asset(vec![(
        custom_token(),
        ExchangeRate {
            rate: 50, // 1 MY_TOKEN = 50 computrons
            updated_at: 90,
            max_age: 100,
        },
    )]);

    // Step 1: User pays solver in MY_TOKEN.
    let user_payment_to_solver = FeePayment {
        asset: custom_token(),
        amount: 20,
        computron_equivalent: 1000, // 20 * 50 = 1000
    };
    let solver_received = solver_policy
        .validate_payment(&user_payment_to_solver, harness.clock.block_height)
        .unwrap();
    assert_eq!(solver_received, 1000);

    // Step 2: Solver pays service in computrons (fronting the converted amount).
    let solver_payment_to_service = FeePayment {
        asset: COMPUTRON_ASSET,
        amount: solver_received,
        computron_equivalent: solver_received, // 1:1
    };
    let service_received = service_policy
        .validate_payment(&solver_payment_to_service, harness.clock.block_height)
        .unwrap();
    assert_eq!(service_received, 1000);

    // End-to-end: user paid 20 MY_TOKEN, service got 1000 computrons.
    assert_eq!(user_payment_to_solver.amount * 50, service_received);
}

// ---------------------------------------------------------------------------
// Test 6 (bonus): Equivalent mismatch detected
// ---------------------------------------------------------------------------
#[test]
fn equivalent_mismatch_detected() {
    let _harness = SimulationHarness::new_federation(3);

    let policy = FeePolicy::multi_asset(vec![(
        usdc(),
        ExchangeRate {
            rate: 100,
            updated_at: 0,
            max_age: 10_000,
        },
    )]);

    // Claim 999 computrons for 10 USDC, but actual is 1000.
    let payment = FeePayment {
        asset: usdc(),
        amount: 10,
        computron_equivalent: 999,
    };

    let result = policy.validate_payment(&payment, 50);
    assert_eq!(
        result,
        Err(FeeError::EquivalentMismatch {
            claimed: 999,
            computed: 1000,
        })
    );
}

// ---------------------------------------------------------------------------
// Test 7 (bonus): Zero amount payment rejected
// ---------------------------------------------------------------------------
#[test]
fn zero_amount_rejected() {
    let _harness = SimulationHarness::new_federation(3);

    let policy = FeePolicy::computrons_only();
    let payment = FeePayment {
        asset: COMPUTRON_ASSET,
        amount: 0,
        computron_equivalent: 0,
    };

    let result = policy.validate_payment(&payment, 10);
    assert_eq!(result, Err(FeeError::ZeroAmount));
}

// ---------------------------------------------------------------------------
// Test 8 (bonus): Rate update refreshes staleness window
// ---------------------------------------------------------------------------
#[test]
fn rate_update_refreshes_staleness() {
    let mut harness = SimulationHarness::new_federation(3);
    harness.advance_blocks(10);

    let mut policy = FeePolicy::multi_asset(vec![(
        usdc(),
        ExchangeRate {
            rate: 100,
            updated_at: 10,
            max_age: 20,
        },
    )]);

    // At height 31 (> 10 + 20), rate is stale.
    let payment = FeePayment {
        asset: usdc(),
        amount: 5,
        computron_equivalent: 500,
    };
    let result = policy.validate_payment(&payment, 31);
    assert!(matches!(result, Err(FeeError::StaleRate { .. })));

    // Update the rate at current height.
    policy.update_rate(
        usdc(),
        ExchangeRate {
            rate: 100,
            updated_at: 31,
            max_age: 20,
        },
    );

    // Now at height 31, it's fresh again.
    let result = policy.validate_payment(&payment, 31);
    assert_eq!(result, Ok(500));

    // And at height 51 (31 + 20), still valid.
    let result = policy.validate_payment(&payment, 51);
    assert_eq!(result, Ok(500));
}
