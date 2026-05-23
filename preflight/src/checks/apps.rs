//! App integration checks: gallery, stablecoin, AMM, orderbook, lending, identity.
//!
//! Each check imports and exercises the ACTUAL app crate's public API rather than
//! reimplementing domain logic with raw TurnBuilder calls. This ensures that:
//! - App public APIs are ergonomic and compile correctly
//! - Core domain invariants hold end-to-end
//! - Circuit integration (prove + verify) works for apps that have it
//!
//! Gallery and Identity checks that require a running PyanaEngine or HTTP server
//! are marked `#[ignore]`-equivalent (return Ok with a note) when they cannot run
//! without an engine instance.

use crate::report::{CheckResult, run_check};

pub fn run() -> Vec<CheckResult> {
    vec![
        run_check("gallery", check_gallery_logic),
        run_check("stablecoin", check_stablecoin_logic),
        run_check("stablecoin_circuit", check_stablecoin_circuit),
        run_check("amm", check_amm_logic),
        run_check("amm_circuit", check_amm_circuit),
        run_check("orderbook", check_orderbook_logic),
        run_check("lending", check_lending_logic),
        run_check("identity", check_identity_logic),
    ]
}

// =============================================================================
// Gallery
// =============================================================================

fn check_gallery_logic() -> Result<(), String> {
    // Gallery's ArtworkRegistry.register() is async and requires a PyanaEngine,
    // so we test the domain primitives that work without an engine:
    // - Artwork ID computation
    // - Bid commitment / reveal cycle
    // - Auction phase validation
    use pyana_gallery::{
        AuctionPhase, compute_artwork_id, compute_bid_commitment, verify_bid_reveal,
    };

    // 1. Artwork ID is deterministic and content-addressed.
    let artist = pyana_types::CellId([0xAA; 32]);
    let image_hash = *blake3::hash(b"digital-painting-bytes").as_bytes();
    let artwork_id = compute_artwork_id(&artist, "Test Artwork", &image_hash);
    let artwork_id_2 = compute_artwork_id(&artist, "Test Artwork", &image_hash);
    if artwork_id != artwork_id_2 {
        return Err("artwork ID should be deterministic".into());
    }

    // Different title => different ID.
    let artwork_id_3 = compute_artwork_id(&artist, "Different Title", &image_hash);
    if artwork_id == artwork_id_3 {
        return Err("different titles should produce different artwork IDs".into());
    }

    // 2. Bid commitment / reveal: commit-reveal integrity.
    let bidder = pyana_types::CellId([0xBB; 32]);
    let amount = 5000u64;
    let nonce = *blake3::hash(b"bid-nonce-secret").as_bytes();

    let commitment = compute_bid_commitment(&bidder, amount, &nonce);

    // Valid reveal should verify.
    if !verify_bid_reveal(&commitment, &bidder, amount, &nonce) {
        return Err("valid bid reveal should pass verification".into());
    }

    // Wrong amount should fail.
    if verify_bid_reveal(&commitment, &bidder, amount + 1, &nonce) {
        return Err("bid reveal with wrong amount should fail".into());
    }

    // Wrong nonce should fail.
    let wrong_nonce = [0u8; 32];
    if verify_bid_reveal(&commitment, &bidder, amount, &wrong_nonce) {
        return Err("bid reveal with wrong nonce should fail".into());
    }

    // 3. AuctionPhase equality checks (ensures serde/types work).
    let phase = AuctionPhase::Bidding;
    if phase != AuctionPhase::Bidding {
        return Err("phase equality broken".into());
    }
    if phase == AuctionPhase::Reveal {
        return Err("bidding should not equal reveal".into());
    }

    Ok(())
}

// =============================================================================
// Stablecoin
// =============================================================================

fn check_stablecoin_logic() -> Result<(), String> {
    use pyana_stablecoin::{
        CdpError, CollateralPosition, ETH_ASSET_TYPE, MIN_RATIO_BPS, PositionStatus,
        StablecoinRegistry, test_attestation,
    };

    let owner = pyana_types::CellId([0xCC; 32]);
    let signing_key = [0x01u8; 32];

    // 1. Open a CDP.
    let mut position = CollateralPosition::open(owner, 100, ETH_ASSET_TYPE, MIN_RATIO_BPS, 100)
        .map_err(|e| format!("open failed: {e}"))?;

    if position.status != PositionStatus::Active {
        return Err("position should be active after open".into());
    }
    if position.collateral_amount != 100 {
        return Err(format!(
            "collateral should be 100, got {}",
            position.collateral_amount
        ));
    }
    if position.debt_amount != 0 {
        return Err("debt should be 0 on open".into());
    }

    // 2. Mint stablecoins (price = 2000, so collateral_value = 200_000).
    //    At 150% ratio, max debt = 200_000 * 10000 / 15000 = ~133_333.
    let attestation = test_attestation("ETH/USD", 2000, 90, signing_key);
    let transition = position
        .mint(100_000, &attestation, 95, 50)
        .map_err(|e| format!("mint failed: {e}"))?;

    if position.debt_amount != 100_000 {
        return Err(format!(
            "debt should be 100000, got {}",
            position.debt_amount
        ));
    }
    if transition.proof.is_empty() {
        return Err("mint should produce a STARK proof".into());
    }
    if transition.created_notes.is_empty() {
        return Err("mint should create a stablecoin note".into());
    }

    // 3. Attempt to over-mint (should fail).
    let over_mint_result = position.mint(200_000, &attestation, 95, 50);
    if !matches!(
        over_mint_result,
        Err(CdpError::InsufficientCollateral { .. })
    ) {
        return Err("over-minting should fail with InsufficientCollateral".into());
    }

    // 4. Repay some debt.
    let repay_transition = position
        .repay(50_000, &attestation, 50)
        .map_err(|e| format!("repay failed: {e}"))?;

    if position.debt_amount != 50_000 {
        return Err(format!(
            "debt after repay should be 50000, got {}",
            position.debt_amount
        ));
    }
    if repay_transition.proof.is_empty() {
        return Err("repay with remaining debt should produce a proof".into());
    }

    // 5. Repay all and close.
    position
        .repay(50_000, &attestation, 50)
        .map_err(|e| format!("final repay failed: {e}"))?;

    let close_transition = position.close().map_err(|e| format!("close failed: {e}"))?;

    if close_transition.position.status != PositionStatus::Closed {
        return Err("position should be closed".into());
    }

    // 6. Liquidation detection: a position is liquidatable when price drops.
    let mut underfunded = CollateralPosition::open(owner, 100, ETH_ASSET_TYPE, MIN_RATIO_BPS, 200)
        .map_err(|e| format!("open2 failed: {e}"))?;
    underfunded.debt_amount = 100_000;

    // At price 1000: collateral_value = 100_000, ratio = 10000 bps = 100% < 150%.
    if !underfunded.is_liquidatable(1000) {
        return Err("position should be liquidatable at price 1000".into());
    }
    // At price 2000: collateral_value = 200_000, ratio = 20000 bps = 200% > 150%.
    if underfunded.is_liquidatable(2000) {
        return Err("position should NOT be liquidatable at price 2000".into());
    }

    // 7. Registry tracks positions.
    let mut registry = StablecoinRegistry::new();
    let pos = CollateralPosition::open(owner, 500, ETH_ASSET_TYPE, MIN_RATIO_BPS, 300)
        .map_err(|e| format!("open3 failed: {e}"))?;
    let pos_id = pos.id;
    registry.register(pos);
    if registry.get(&pos_id).is_none() {
        return Err("registry should find registered position".into());
    }

    Ok(())
}

fn check_stablecoin_circuit() -> Result<(), String> {
    use pyana_circuit::field::BabyBear;
    use pyana_stablecoin::{CdpWitness, MIN_RATIO_BPS, prove_cdp_ratio, verify_cdp_ratio};

    // Healthy position: prove and verify.
    let witness = CdpWitness {
        collateral_amount: 1000,
        price: 2000,
        debt_amount: 1_000_000,
        ratio_bps: MIN_RATIO_BPS,
        position_id: [0xAB; 32],
        oracle_commitment: BabyBear::new(12345),
        price_timestamp: 100,
        max_age: 50,
    };

    let proof = prove_cdp_ratio(&witness).map_err(|e| format!("prove failed: {e}"))?;
    if proof.is_empty() {
        return Err("proof should not be empty for healthy position".into());
    }

    verify_cdp_ratio(&proof, &witness).map_err(|e| format!("verify failed: {e}"))?;

    // Unhealthy position: prove should fail.
    let bad_witness = CdpWitness {
        collateral_amount: 1,
        price: 1,
        debt_amount: 1_000_000,
        ratio_bps: MIN_RATIO_BPS,
        position_id: [0xCD; 32],
        oracle_commitment: BabyBear::new(99999),
        price_timestamp: 100,
        max_age: 50,
    };

    // The unhealthy witness should fail to prove (constraint system rejects it).
    if prove_cdp_ratio(&bad_witness).is_ok() {
        return Err("unhealthy position should NOT produce a valid proof".into());
    }

    Ok(())
}

// =============================================================================
// AMM
// =============================================================================

fn check_amm_logic() -> Result<(), String> {
    use pyana_amm::AmmRegistry;
    use pyana_amm::pool::LiquidityPool;

    // 1. Create a pool.
    let pool = LiquidityPool::create(1, 2, 10_000, 20_000)
        .map_err(|e| format!("pool create failed: {e}"))?;

    if pool.reserve_a != 10_000 || pool.reserve_b != 20_000 {
        return Err(format!(
            "reserves wrong: a={}, b={}",
            pool.reserve_a, pool.reserve_b
        ));
    }

    let initial_k = pool.k();
    if initial_k != 200_000_000 {
        return Err(format!("k should be 200_000_000, got {initial_k}"));
    }

    // 2. Execute a swap (A -> B).
    let mut pool = pool;
    let swap_result = pool
        .swap(100, 1, true)
        .map_err(|e| format!("swap failed: {e}"))?;

    // Output should be non-zero.
    if swap_result.amount_out == 0 {
        return Err("swap should produce non-zero output".into());
    }

    // Invariant: k should grow (fees).
    let k_after = pool.k();
    if k_after < initial_k {
        return Err(format!(
            "invariant violated: k_after={k_after} < k_before={initial_k}"
        ));
    }

    // Fee was charged.
    if swap_result.fee_amount == 0 {
        return Err("fee should be non-zero".into());
    }

    // 3. Slippage protection works.
    let slippage_result = pool.swap(100, u64::MAX, true);
    if slippage_result.is_ok() {
        return Err("swap with impossible min_output should fail".into());
    }

    // 4. Add liquidity (proportional).
    let ratio_a = pool.reserve_a;
    let ratio_b = pool.reserve_b;
    // Add proportional amounts.
    let add_a = ratio_a / 10; // 10% of reserve
    let add_b = ratio_b / 10;
    let add_result = pool
        .add_liquidity(add_a, add_b)
        .map_err(|e| format!("add_liquidity failed: {e}"))?;
    if add_result.lp_minted == 0 {
        return Err("adding liquidity should mint LP tokens".into());
    }

    // 5. Remove liquidity.
    let lp_to_burn = add_result.lp_minted / 2;
    let remove_result = pool
        .remove_liquidity(lp_to_burn)
        .map_err(|e| format!("remove_liquidity failed: {e}"))?;
    if remove_result.amount_a == 0 || remove_result.amount_b == 0 {
        return Err("removing liquidity should return both tokens".into());
    }

    // 6. Registry lookup.
    let mut registry = AmmRegistry::new();
    let fresh_pool = LiquidityPool::create(10, 20, 5000, 5000)
        .map_err(|e| format!("pool2 create failed: {e}"))?;
    let pool_id = fresh_pool.id;
    registry.register_pool(fresh_pool);

    if registry.get_pool(&pool_id).is_none() {
        return Err("registry should find pool by ID".into());
    }
    if registry.find_pool_by_pair(10, 20).is_none() {
        return Err("registry should find pool by pair".into());
    }
    if registry.pool_count() != 1 {
        return Err(format!(
            "pool_count should be 1, got {}",
            registry.pool_count()
        ));
    }

    Ok(())
}

fn check_amm_circuit() -> Result<(), String> {
    use pyana_amm::circuit::amm_swap_descriptor;

    // Verify the AMM circuit descriptor is valid.
    let descriptor = amm_swap_descriptor();
    descriptor
        .validate()
        .map_err(|e| format!("AMM descriptor validation failed: {e}"))?;

    // The descriptor should have the expected trace width.
    if descriptor.trace_width != pyana_amm::circuit::col::WIDTH {
        return Err(format!(
            "AMM trace width mismatch: {} vs {}",
            descriptor.trace_width,
            pyana_amm::circuit::col::WIDTH
        ));
    }

    Ok(())
}

// =============================================================================
// Orderbook
// =============================================================================

fn check_orderbook_logic() -> Result<(), String> {
    use pyana_orderbook::{
        Fill, MatchingEngine, Order, OrderBook, OrderType, OrderbookEngine, Side, TimeInForce,
        TradingPair,
    };

    let pair = TradingPair {
        base: "ETH".into(),
        quote: "USD".into(),
    };

    // 1. Test unverified path (no escrow required) for basic matching.
    let mut engine = OrderbookEngine::new(pair.clone());

    let trader_a = pyana_types::CellId([0xAA; 32]);
    let trader_b = pyana_types::CellId([0xBB; 32]);

    // Submit a buy limit at 105.
    let buy_order = Order::new(
        trader_a,
        OrderType::Limit {
            price: 105,
            amount: 50,
            side: Side::Buy,
            time_in_force: TimeInForce::GTC,
        },
        1,
        0,
    );

    let buy_result = engine
        .submit_order_unverified(buy_order)
        .map_err(|e| format!("buy submit failed: {e}"))?;

    // Buy should rest on the book (no matching counterpart yet).
    if !buy_result.fills.is_empty() {
        return Err("buy should not fill without a matching sell".into());
    }

    // Submit a sell limit at 100 (crosses with buy at 105).
    let sell_order = Order::new(
        trader_b,
        OrderType::Limit {
            price: 100,
            amount: 30,
            side: Side::Sell,
            time_in_force: TimeInForce::GTC,
        },
        1,
        0,
    );

    let sell_result = engine
        .submit_order_unverified(sell_order)
        .map_err(|e| format!("sell submit failed: {e}"))?;

    // Orders should cross (buy@105 >= sell@100).
    if sell_result.fills.is_empty() {
        return Err("orders should cross: buy@105 vs sell@100".into());
    }

    let fill = &sell_result.fills[0];
    if fill.amount != 30 {
        return Err(format!("fill amount should be 30, got {}", fill.amount));
    }
    // Fill price is the maker's price (105, since the buy was resting).
    if fill.price != 105 {
        return Err(format!(
            "fill price should be 105 (maker), got {}",
            fill.price
        ));
    }

    // 2. Partial fill: buyer still wants 20 more.
    if sell_result.fully_filled {
        // The sell order of 30 was fully filled.
        // The buy order residual should still be on the book.
        let residual_on_book = engine.book.best_bid();
        if residual_on_book.is_none() {
            return Err("buy order residual (20) should still be on the book".into());
        }
    }

    // 3. Order expiration: GTD orders expire at height.
    let mut engine2 = OrderbookEngine::new(pair.clone());
    let gtd_order = Order::new(
        trader_a,
        OrderType::Limit {
            price: 200,
            amount: 10,
            side: Side::Buy,
            time_in_force: TimeInForce::GTD { expiry_height: 50 },
        },
        2,
        0,
    );
    engine2
        .submit_order_unverified(gtd_order)
        .map_err(|e| format!("GTD submit failed: {e}"))?;

    let expired = engine2.advance_height(51);
    if expired.is_empty() {
        return Err("GTD order should expire after its height".into());
    }

    // 4. State commitment: book state is committed after operations.
    let commitment = engine.current_state_commitment();
    if commitment.root == [0u8; 32] && commitment.order_count > 0 {
        return Err("state commitment root should be non-zero for non-empty book".into());
    }

    Ok(())
}

// =============================================================================
// Lending
// =============================================================================

fn check_lending_logic() -> Result<(), String> {
    use pyana_lending::borrow::CollateralEntry;
    use pyana_lending::{LendingPool, Market};

    let supplier = pyana_types::CellId([0xDD; 32]);
    let borrower = pyana_types::CellId([0xEE; 32]);

    // 1. Create a lending pool with a market.
    let mut pool = LendingPool::new();
    let market = Market::new(1); // asset_id = 1
    pool.add_market(market);

    // 2. Supply tokens.
    let receipt = pool
        .supply(supplier, 1, 10_000)
        .map_err(|e| format!("supply failed: {e}"))?;

    // Verify supply receipt.
    if receipt.amount != 10_000 {
        return Err(format!(
            "receipt amount should be 10000, got {}",
            receipt.amount
        ));
    }

    // Market should reflect the supply.
    let m = pool.get_market(1).ok_or("market not found")?;
    if m.total_supply != 10_000 {
        return Err(format!(
            "total_supply should be 10000, got {}",
            m.total_supply
        ));
    }

    // 3. Borrow against collateral.
    let collateral = vec![CollateralEntry {
        asset_id: 2,
        amount: 10_000,
        price: 20_000, // value = 10000 * 20000 / 10000 = 20_000
    }];

    let position_id = pool
        .borrow(borrower, 1, 5_000, collateral)
        .map_err(|e| format!("borrow failed: {e}"))?;

    // Market should reflect the borrow.
    let m = pool.get_market(1).ok_or("market not found after borrow")?;
    if m.total_borrows != 5_000 {
        return Err(format!(
            "total_borrows should be 5000, got {}",
            m.total_borrows
        ));
    }

    // 4. Accrue interest by advancing blocks.
    pool.advance_to_block(100);

    // After interest accrual, total_borrows should increase.
    let m = pool.get_market(1).ok_or("market not found after accrual")?;
    if m.total_borrows <= 5_000 {
        return Err(format!(
            "total_borrows should grow with interest, got {}",
            m.total_borrows
        ));
    }

    // 5. Repay the debt.
    let repaid = pool
        .repay(&position_id, 5_000)
        .map_err(|e| format!("repay failed: {e}"))?;

    if repaid == 0 {
        return Err("repay amount should be non-zero".into());
    }

    // 6. Insufficient collateral should be rejected.
    let weak_collateral = vec![CollateralEntry {
        asset_id: 2,
        amount: 1,
        price: 1, // effectively zero collateral value
    }];

    let bad_borrow = pool.borrow(borrower, 1, 4_000, weak_collateral);
    if bad_borrow.is_ok() {
        return Err("borrow with insufficient collateral should fail".into());
    }

    // 7. Market utilization makes sense.
    let m = pool.get_market(1).ok_or("market not found final")?;
    let util = m.utilization_bps();
    // Should be between 0 and 10000 bps.
    if util > 10_000 {
        return Err(format!("utilization {util} should be <= 10000 bps"));
    }

    Ok(())
}

// =============================================================================
// Identity
// =============================================================================

fn check_identity_logic() -> Result<(), String> {
    use pyana_circuit::field::BabyBear;
    use pyana_identity::AttributeValue;
    use pyana_identity::credential::CredentialSchema;
    use pyana_identity::holder::CredentialWallet;
    use pyana_identity::issuer::IssuerRegistry;
    use pyana_identity::presentation::PresentationBuilder;
    use pyana_identity::revocation::NonRevocationProof;
    use pyana_identity::verifier::{VerificationPolicy, VerificationResult};
    use std::collections::BTreeMap;

    let issuer_id = [0x11u8; 32];
    let holder_id = [0x22u8; 32];

    // 1. Create an issuer and register a schema.
    let mut issuer = IssuerRegistry::new(issuer_id);

    let schema = CredentialSchema {
        name: "GovernmentID".to_string(),
        issuer_id,
        attributes: vec!["name".into(), "age".into(), "country".into()],
    };
    issuer.register_schema(schema);

    // 2. Issue a credential to a holder.
    let mut attributes = BTreeMap::new();
    attributes.insert("name".into(), AttributeValue::Text("Alice".into()));
    attributes.insert("age".into(), AttributeValue::Integer(25));
    attributes.insert("country".into(), AttributeValue::Text("US".into()));

    let credential = issuer
        .issue("GovernmentID", holder_id, attributes, 1000, 2000)
        .ok_or("issuance failed")?;

    if credential.schema_name != "GovernmentID" {
        return Err("credential schema name mismatch".into());
    }
    if credential.issuer_id != issuer_id {
        return Err("credential issuer_id mismatch".into());
    }
    if credential.holder_id != holder_id {
        return Err("credential holder_id mismatch".into());
    }

    let cred_id = credential.id;

    // 3. Store credential in a wallet.
    let mut wallet = CredentialWallet::new(holder_id);
    wallet.store(credential.clone());

    if wallet.len() != 1 {
        return Err(format!(
            "wallet should have 1 credential, got {}",
            wallet.len()
        ));
    }
    if wallet.get(&cred_id).is_none() {
        return Err("wallet should find stored credential".into());
    }

    // 4. Build a presentation with selective disclosure.
    let mut builder = PresentationBuilder::new();
    let cred_idx = builder.add_credential(credential.clone());
    builder.reveal_attribute(cred_idx, "name");

    // Attach a valid non-revocation proof (credential is NOT revoked).
    let non_rev_proof = NonRevocationProof {
        revocation_root: issuer.revocation_root(),
        is_valid: true,
    };
    builder.set_non_revocation(non_rev_proof);

    let presentation = builder.build().ok_or("presentation build failed")?;

    // Verify: name should be revealed.
    if !presentation.revealed_attributes.contains_key("name") {
        return Err("name should be in revealed attributes".into());
    }
    // Age should NOT be revealed (selective disclosure).
    if presentation.revealed_attributes.contains_key("age") {
        return Err("age should NOT be revealed".into());
    }

    // 5. Verification policy checks.
    let policy = VerificationPolicy::new(
        "AgeCheck",
        BabyBear::ZERO, // federation root (simplified)
        issuer.revocation_root(),
    )
    .require_reveal("name")
    .with_non_revocation(true);

    let result = policy.verify_presentation(&presentation);
    if !result.is_accepted() {
        return Err(format!("presentation should be accepted, got {:?}", result));
    }

    // 6. Missing required attribute fails verification.
    let strict_policy =
        VerificationPolicy::new("StrictCheck", BabyBear::ZERO, issuer.revocation_root())
            .require_reveal("age") // age was not revealed
            .with_non_revocation(true);

    let strict_result = strict_policy.verify_presentation(&presentation);
    if strict_result.is_accepted() {
        return Err("policy requiring unrevealed 'age' should reject".into());
    }

    // 7. Revocation: revoke the credential and verify it's detected.
    let revoked = issuer.revoke(&cred_id);
    if !revoked {
        return Err("revocation should succeed".into());
    }
    if !issuer.is_revoked(&cred_id) {
        return Err("credential should show as revoked".into());
    }

    // A presentation with invalid non-revocation proof should be rejected.
    let mut builder2 = PresentationBuilder::new();
    let cred_idx2 = builder2.add_credential(credential.clone());
    builder2.reveal_attribute(cred_idx2, "name");
    // Don't set non-revocation proof (simulates revoked credential).
    let presentation2 = builder2.build().ok_or("presentation2 build failed")?;

    let revoke_policy =
        VerificationPolicy::new("RevokeCheck", BabyBear::ZERO, issuer.revocation_root())
            .require_reveal("name")
            .with_non_revocation(true);

    let revoke_result = revoke_policy.verify_presentation(&presentation2);
    if revoke_result.is_accepted() {
        return Err("revoked credential without non-revocation proof should be rejected".into());
    }

    // 8. Double revocation returns false (already revoked).
    let double_revoke = issuer.revoke(&cred_id);
    if double_revoke {
        return Err("double revocation should return false".into());
    }

    Ok(())
}
