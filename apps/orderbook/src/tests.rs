//! Comprehensive test suite for the financial orderbook matching engine.

#[cfg(test)]
mod tests {
    use crate::OrderbookEngine;
    use crate::book::{OrderBook, TradingPair};
    use crate::circuit::{
        MatchProofDescriptor, MatchProofWitness, compute_cancel_proof_hash, verify_cancel_proof,
    };
    use crate::commit_reveal::{
        COMMIT_WINDOW_BLOCKS, CommitRevealRegistry, OrderCommitment, OrderReveal,
        compute_order_commitment,
    };
    use crate::escrow::{self, EscrowRegistry, OrderEscrow};
    use crate::matching::{MatchError, MatchingEngine};
    use crate::order::{Order, OrderStatus, OrderType, Side, TimeInForce};
    use crate::private_order::{
        PrivateOrder, PrivateOrderParams, build_dark_pool_crossing, compute_amount_commitment,
        compute_payment_commitment, verify_amount_commitment, verify_dark_pool_crossing,
        verify_payment_conservation,
    };
    use crate::settlement::build_settlement_effects;
    use crate::state_commitment::{
        collect_live_orders, compute_merkle_root, generate_inclusion_proof, verify_inclusion_proof,
    };
    use crate::verified_matching::VerifiedMatchingEngine;
    use pyana_types::CellId;

    fn make_cell(seed: u8) -> CellId {
        CellId([seed; 32])
    }

    fn eth_usdc_pair() -> TradingPair {
        TradingPair::new("ETH", "USDC")
    }

    // =========================================================================
    // Test: Place limit buy and sell, cross the spread -> trade executes
    // =========================================================================

    #[test]
    fn test_limit_orders_cross_spread_executes_trade() {
        let mut book = OrderBook::new(eth_usdc_pair());
        let alice = make_cell(1);
        let bob = make_cell(2);

        // Alice places a sell at price 100.
        let sell = Order::new(
            alice,
            OrderType::Limit {
                price: 100,
                amount: 50,
                side: Side::Sell,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1000,
        );
        book.insert_order(sell);

        // Bob places a buy at price 100 (crosses the spread).
        let buy = Order::new(
            bob,
            OrderType::Limit {
                price: 100,
                amount: 50,
                side: Side::Buy,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1001,
        );

        let result = MatchingEngine::match_order(&mut book, buy).unwrap();

        assert!(result.fully_filled);
        assert_eq!(result.total_filled, 50);
        assert_eq!(result.fills.len(), 1);
        assert_eq!(result.fills[0].price, 100);
        assert_eq!(result.fills[0].amount, 50);
        assert_eq!(result.fills[0].taker, bob);
        assert_eq!(result.fills[0].maker, alice);
        assert!(result.residual.is_none());
        assert_eq!(book.order_count(), 0); // Both sides consumed.
    }

    // =========================================================================
    // Test: Partial fill (order 100, match against order of 60, residual 40 remains)
    // =========================================================================

    #[test]
    fn test_partial_fill_residual_remains() {
        let mut book = OrderBook::new(eth_usdc_pair());
        let alice = make_cell(1);
        let bob = make_cell(2);

        // Alice places a sell of 60 at price 100.
        let sell = Order::new(
            alice,
            OrderType::Limit {
                price: 100,
                amount: 60,
                side: Side::Sell,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1000,
        );
        book.insert_order(sell);

        // Bob places a buy of 100 at price 100 (only 60 available).
        let buy = Order::new(
            bob,
            OrderType::Limit {
                price: 100,
                amount: 100,
                side: Side::Buy,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1001,
        );

        let result = MatchingEngine::match_order(&mut book, buy).unwrap();

        assert!(!result.fully_filled);
        assert_eq!(result.total_filled, 60);
        assert_eq!(result.fills.len(), 1);
        assert_eq!(result.fills[0].amount, 60);

        // Residual of 40 should be on the book.
        let residual = result.residual.unwrap();
        assert_eq!(residual.remaining_amount, 40);
        assert!(matches!(
            residual.status,
            OrderStatus::PartiallyFilled { filled_amount: 60 }
        ));
        assert_eq!(book.order_count(), 1); // Residual resting.
        assert_eq!(book.best_bid(), Some(100));
    }

    // =========================================================================
    // Test: Price-time priority (earlier order at same price fills first)
    // =========================================================================

    #[test]
    fn test_price_time_priority() {
        let mut book = OrderBook::new(eth_usdc_pair());
        let alice = make_cell(1);
        let bob = make_cell(2);
        let charlie = make_cell(3);

        // Alice places a sell at 100, created at block 1000.
        let sell_alice = Order::new(
            alice,
            OrderType::Limit {
                price: 100,
                amount: 30,
                side: Side::Sell,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1000,
        );
        book.insert_order(sell_alice.clone());

        // Bob places a sell at 100, created at block 1001 (later).
        let sell_bob = Order::new(
            bob,
            OrderType::Limit {
                price: 100,
                amount: 30,
                side: Side::Sell,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1001,
        );
        book.insert_order(sell_bob.clone());

        // Charlie buys 30 at 100 — should fill against Alice (earlier) not Bob.
        let buy = Order::new(
            charlie,
            OrderType::Limit {
                price: 100,
                amount: 30,
                side: Side::Buy,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1002,
        );

        let result = MatchingEngine::match_order(&mut book, buy).unwrap();

        assert!(result.fully_filled);
        assert_eq!(result.fills.len(), 1);
        assert_eq!(result.fills[0].maker, alice); // Alice fills first (FIFO).
        assert_eq!(result.fills[0].maker_order_id, sell_alice.id);

        // Bob's order should still be on the book.
        assert_eq!(book.order_count(), 1);
        assert!(book.contains_order(&sell_bob.id));
    }

    // =========================================================================
    // Test: Market order sweeps multiple price levels
    // =========================================================================

    #[test]
    fn test_market_order_sweeps_levels() {
        let mut book = OrderBook::new(eth_usdc_pair());
        let alice = make_cell(1);
        let bob = make_cell(2);
        let charlie = make_cell(3);

        // Alice sells 20 at 100.
        book.insert_order(Order::new(
            alice,
            OrderType::Limit {
                price: 100,
                amount: 20,
                side: Side::Sell,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1000,
        ));

        // Bob sells 30 at 101.
        book.insert_order(Order::new(
            bob,
            OrderType::Limit {
                price: 101,
                amount: 30,
                side: Side::Sell,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1001,
        ));

        // Charlie places a market buy for 50 (sweeps both levels).
        let market_buy = Order::new(
            charlie,
            OrderType::Market {
                amount: 50,
                side: Side::Buy,
                slippage_bps: 500, // 5% slippage allowed
            },
            1,
            1002,
        );

        let result = MatchingEngine::match_order(&mut book, market_buy).unwrap();

        assert!(result.fully_filled);
        assert_eq!(result.total_filled, 50);
        assert_eq!(result.fills.len(), 2);
        assert_eq!(result.fills[0].price, 100);
        assert_eq!(result.fills[0].amount, 20);
        assert_eq!(result.fills[1].price, 101);
        assert_eq!(result.fills[1].amount, 30);
        assert_eq!(book.order_count(), 0);
    }

    // =========================================================================
    // Test: Stop-loss triggers on price update
    // =========================================================================

    #[test]
    fn test_stop_loss_order_created_pending() {
        let alice = make_cell(1);

        // Create a stop-loss order.
        let stop = Order::new(
            alice,
            OrderType::StopLoss {
                trigger_price: 90,
                amount: 50,
                side: Side::Sell,
            },
            1,
            1000,
        );

        // Stop-loss orders start in Pending status.
        assert_eq!(stop.status, OrderStatus::Pending);
        assert_eq!(stop.remaining_amount, 50);

        // When the oracle price drops to 90, the stop is triggered and becomes
        // a market sell. This is handled by ConditionalTurn in the engine layer.
        // Here we verify the order type encodes the trigger correctly.
        if let OrderType::StopLoss { trigger_price, .. } = &stop.order_type {
            assert_eq!(*trigger_price, 90);
        } else {
            panic!("expected StopLoss order type");
        }
    }

    // =========================================================================
    // Test: IOC (Immediate-or-Cancel) — unfilled portion cancelled
    // =========================================================================

    #[test]
    fn test_ioc_cancels_unfilled_portion() {
        let mut book = OrderBook::new(eth_usdc_pair());
        let alice = make_cell(1);
        let bob = make_cell(2);

        // Alice sells 30 at 100.
        book.insert_order(Order::new(
            alice,
            OrderType::Limit {
                price: 100,
                amount: 30,
                side: Side::Sell,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1000,
        ));

        // Bob places IOC buy for 50 at 100.
        let ioc_buy = Order::new(
            bob,
            OrderType::Limit {
                price: 100,
                amount: 50,
                side: Side::Buy,
                time_in_force: TimeInForce::IOC,
            },
            1,
            1001,
        );

        let result = MatchingEngine::match_order(&mut book, ioc_buy).unwrap();

        // Should fill 30 and cancel the remaining 20 (IOC behavior).
        assert!(!result.fully_filled);
        assert_eq!(result.total_filled, 30);
        assert!(result.residual.is_none()); // IOC: no residual posted.
        assert_eq!(book.order_count(), 0);
    }

    // =========================================================================
    // Test: FOK (Fill-or-Kill) — reject if can't fill entirely
    // =========================================================================

    #[test]
    fn test_fok_rejects_insufficient_liquidity() {
        let mut book = OrderBook::new(eth_usdc_pair());
        let alice = make_cell(1);
        let bob = make_cell(2);

        // Alice sells 30 at 100.
        book.insert_order(Order::new(
            alice,
            OrderType::Limit {
                price: 100,
                amount: 30,
                side: Side::Sell,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1000,
        ));

        // Bob places FOK buy for 50 at 100 (only 30 available → rejected).
        let fok_buy = Order::new(
            bob,
            OrderType::Limit {
                price: 100,
                amount: 50,
                side: Side::Buy,
                time_in_force: TimeInForce::FOK,
            },
            1,
            1001,
        );

        let result = MatchingEngine::match_order(&mut book, fok_buy);
        assert!(result.is_err());
        match result.unwrap_err() {
            MatchError::FillOrKillRejected {
                available,
                required,
            } => {
                assert_eq!(available, 30);
                assert_eq!(required, 50);
            }
            other => panic!("expected FillOrKillRejected, got {:?}", other),
        }

        // Alice's order should still be on the book (FOK doesn't consume partial).
        assert_eq!(book.order_count(), 1);
    }

    #[test]
    fn test_fok_succeeds_when_fully_fillable() {
        let mut book = OrderBook::new(eth_usdc_pair());
        let alice = make_cell(1);
        let bob = make_cell(2);

        // Alice sells 50 at 100.
        book.insert_order(Order::new(
            alice,
            OrderType::Limit {
                price: 100,
                amount: 50,
                side: Side::Sell,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1000,
        ));

        // Bob places FOK buy for 50 at 100 (exactly enough).
        let fok_buy = Order::new(
            bob,
            OrderType::Limit {
                price: 100,
                amount: 50,
                side: Side::Buy,
                time_in_force: TimeInForce::FOK,
            },
            1,
            1001,
        );

        let result = MatchingEngine::match_order(&mut book, fok_buy).unwrap();
        assert!(result.fully_filled);
        assert_eq!(result.total_filled, 50);
    }

    // =========================================================================
    // Test: Cancel order by owner
    // =========================================================================

    #[test]
    fn test_cancel_order_by_owner() {
        let mut book = OrderBook::new(eth_usdc_pair());
        let alice = make_cell(1);

        let sell = Order::new(
            alice,
            OrderType::Limit {
                price: 100,
                amount: 50,
                side: Side::Sell,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1000,
        );
        let order_id = sell.id;
        book.insert_order(sell);

        assert_eq!(book.order_count(), 1);

        // Owner cancels: verify ownership via cancel proof.
        let cancel_hash = compute_cancel_proof_hash(&alice, &order_id);
        assert!(verify_cancel_proof(&alice, &order_id, &cancel_hash));

        // Remove from book.
        let removed = book.remove_order(&order_id);
        assert!(removed.is_some());
        assert_eq!(book.order_count(), 0);
    }

    // =========================================================================
    // Test: Reject cancel by non-owner
    // =========================================================================

    #[test]
    fn test_reject_cancel_by_non_owner() {
        let alice = make_cell(1);
        let bob = make_cell(2);

        let sell = Order::new(
            alice,
            OrderType::Limit {
                price: 100,
                amount: 50,
                side: Side::Sell,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1000,
        );
        let order_id = sell.id;

        // Alice's cancel proof.
        let cancel_hash = compute_cancel_proof_hash(&alice, &order_id);

        // Bob tries to cancel — his cell ID won't produce the right hash.
        assert!(!verify_cancel_proof(&bob, &order_id, &cancel_hash));
    }

    // =========================================================================
    // Test: Private order (committed amount, settlement reveals only to counterparty)
    // =========================================================================

    #[test]
    fn test_private_order_commitment() {
        let alice = make_cell(1);
        let blinding = [0xAB; 32];
        let amount = 100u64;

        let params = PrivateOrderParams { amount, blinding };

        let private = PrivateOrder::new(alice, Side::Sell, 200, &params, TimeInForce::GTC, 1, 1000);

        // The commitment should hide the amount.
        let commitment = compute_amount_commitment(amount, &blinding);
        assert_eq!(private.amount_commitment, commitment);

        // Verification with correct opening succeeds.
        assert!(verify_amount_commitment(&commitment, amount, &blinding));

        // Verification with wrong amount fails.
        assert!(!verify_amount_commitment(&commitment, 99, &blinding));

        // Verification with wrong blinding fails.
        assert!(!verify_amount_commitment(&commitment, amount, &[0xCD; 32]));

        // The public order has amount = 0 (hidden).
        let public = private.to_public_order();
        assert_eq!(public.remaining_amount, 0);
        assert_eq!(public.committed_amount, Some(commitment));
    }

    // =========================================================================
    // Test: Self-trade prevention
    // =========================================================================

    #[test]
    fn test_self_trade_prevention() {
        let mut book = OrderBook::new(eth_usdc_pair());
        let alice = make_cell(1);

        // Alice has a sell at 100.
        book.insert_order(Order::new(
            alice,
            OrderType::Limit {
                price: 100,
                amount: 50,
                side: Side::Sell,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1000,
        ));

        // Alice places a buy at 100 — should NOT match against her own sell.
        let buy = Order::new(
            alice,
            OrderType::Limit {
                price: 100,
                amount: 50,
                side: Side::Buy,
                time_in_force: TimeInForce::GTC,
            },
            2,
            1001,
        );

        let result = MatchingEngine::match_order(&mut book, buy).unwrap();

        // No fill should occur (self-trade prevented).
        assert!(!result.fully_filled);
        assert_eq!(result.total_filled, 0);
        assert_eq!(result.fills.len(), 0);
        // The buy should rest on the book since it's GTC with no match.
        assert!(result.residual.is_some());
        assert_eq!(book.order_count(), 2); // Both orders resting.
    }

    // =========================================================================
    // Test: Price priority (better price fills first)
    // =========================================================================

    #[test]
    fn test_price_priority_best_price_first() {
        let mut book = OrderBook::new(eth_usdc_pair());
        let alice = make_cell(1);
        let bob = make_cell(2);
        let charlie = make_cell(3);

        // Bob sells at 101.
        let sell_bob = Order::new(
            bob,
            OrderType::Limit {
                price: 101,
                amount: 50,
                side: Side::Sell,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1000,
        );
        book.insert_order(sell_bob);

        // Alice sells at 100 (better price for buyer).
        let sell_alice = Order::new(
            alice,
            OrderType::Limit {
                price: 100,
                amount: 50,
                side: Side::Sell,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1001,
        );
        book.insert_order(sell_alice);

        // Charlie buys 50 at 101 — should fill at 100 (Alice's better price).
        let buy = Order::new(
            charlie,
            OrderType::Limit {
                price: 101,
                amount: 50,
                side: Side::Buy,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1002,
        );

        let result = MatchingEngine::match_order(&mut book, buy).unwrap();

        assert!(result.fully_filled);
        assert_eq!(result.fills[0].price, 100); // Filled at Alice's price.
        assert_eq!(result.fills[0].maker, alice);
    }

    // =========================================================================
    // Test: GTD order expiration
    // =========================================================================

    #[test]
    fn test_gtd_order_expiration() {
        let mut book = OrderBook::new(eth_usdc_pair());
        let alice = make_cell(1);

        // Alice places a GTD sell that expires at block 2000.
        let sell = Order::new(
            alice,
            OrderType::Limit {
                price: 100,
                amount: 50,
                side: Side::Sell,
                time_in_force: TimeInForce::GTD {
                    expiry_height: 2000,
                },
            },
            1,
            1000,
        );
        book.insert_order(sell);

        // Before expiry: order is still there.
        let expired = book.expire_orders(1999);
        assert!(expired.is_empty());
        assert_eq!(book.order_count(), 1);

        // At expiry: order is removed.
        let expired = book.expire_orders(2000);
        assert_eq!(expired.len(), 1);
        assert_eq!(expired[0].status, OrderStatus::Expired);
        assert_eq!(book.order_count(), 0);
    }

    // =========================================================================
    // Test: Settlement effects are correctly computed
    // =========================================================================

    #[test]
    fn test_settlement_effects() {
        let alice = make_cell(1);
        let bob = make_cell(2);

        let fill = crate::matching::Fill {
            taker_order_id: [0xAA; 32],
            maker_order_id: [0xBB; 32],
            price: 100,
            amount: 50,
            taker: bob,
            maker: alice,
            taker_side: Side::Buy,
        };

        let (settlement, effects) = build_settlement_effects(&fill, 1000);

        assert_eq!(settlement.fill_price, 100);
        assert_eq!(settlement.fill_amount, 50);
        assert_eq!(settlement.total_payment, 5000); // 100 * 50
        assert_eq!(settlement.buyer, bob); // taker is buying
        assert_eq!(settlement.seller, alice); // maker is selling
        assert_eq!(effects.len(), 1); // One transfer effect.
    }

    // =========================================================================
    // Test: Match proof descriptor constraint checks
    // =========================================================================

    #[test]
    fn test_match_proof_constraints_valid() {
        let alice = make_cell(1);
        let bob = make_cell(2);

        let fill = crate::matching::Fill {
            taker_order_id: [0xAA; 32],
            maker_order_id: [0xBB; 32],
            price: 100,
            amount: 50,
            taker: bob,
            maker: alice,
            taker_side: Side::Buy,
        };

        let descriptor = MatchProofDescriptor::from_fill(&fill, [0x11; 32], [0x22; 32]);

        let witness = MatchProofWitness {
            maker_limit_price: 100, // ask price = fill price (satisfied)
            maker_remaining_before: 50,
            maker_queue_position: 0, // front of queue
            orders_ahead: vec![],
            taker_cell_bytes: *bob.as_bytes(),
            maker_cell_bytes: *alice.as_bytes(),
        };

        let descriptor = descriptor.with_witness(witness);
        assert!(descriptor.verify_all_constraints().is_ok());
    }

    #[test]
    fn test_match_proof_rejects_self_trade() {
        let alice = make_cell(1);

        let fill = crate::matching::Fill {
            taker_order_id: [0xAA; 32],
            maker_order_id: [0xBB; 32],
            price: 100,
            amount: 50,
            taker: alice,
            maker: alice, // same person!
            taker_side: Side::Buy,
        };

        let descriptor = MatchProofDescriptor::from_fill(&fill, [0x11; 32], [0x22; 32]);

        let witness = MatchProofWitness {
            maker_limit_price: 100,
            maker_remaining_before: 50,
            maker_queue_position: 0,
            orders_ahead: vec![],
            taker_cell_bytes: *alice.as_bytes(),
            maker_cell_bytes: *alice.as_bytes(), // same!
        };

        let descriptor = descriptor.with_witness(witness);
        let result = descriptor.verify_all_constraints();
        assert!(result.is_err());
        assert_eq!(
            result.unwrap_err(),
            crate::circuit::MatchProofError::SelfTrade
        );
    }

    // =========================================================================
    // Test: Book state queries
    // =========================================================================

    #[test]
    fn test_book_best_bid_ask_spread() {
        let mut book = OrderBook::new(eth_usdc_pair());
        let alice = make_cell(1);
        let bob = make_cell(2);

        // No orders: no bid/ask/spread.
        assert_eq!(book.best_bid(), None);
        assert_eq!(book.best_ask(), None);
        assert_eq!(book.spread(), None);

        // Add a bid at 99.
        book.insert_order(Order::new(
            alice,
            OrderType::Limit {
                price: 99,
                amount: 10,
                side: Side::Buy,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1000,
        ));

        // Add an ask at 101.
        book.insert_order(Order::new(
            bob,
            OrderType::Limit {
                price: 101,
                amount: 10,
                side: Side::Sell,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1001,
        ));

        assert_eq!(book.best_bid(), Some(99));
        assert_eq!(book.best_ask(), Some(101));
        assert_eq!(book.spread(), Some(2));
    }

    // =========================================================================
    // Test: Multiple partial fills across multiple makers
    // =========================================================================

    #[test]
    fn test_multiple_partial_fills() {
        let mut book = OrderBook::new(eth_usdc_pair());
        let alice = make_cell(1);
        let bob = make_cell(2);
        let charlie = make_cell(3);
        let dave = make_cell(4);

        // Alice sells 20, Bob sells 30, Charlie sells 50 — all at 100.
        book.insert_order(Order::new(
            alice,
            OrderType::Limit {
                price: 100,
                amount: 20,
                side: Side::Sell,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1000,
        ));
        book.insert_order(Order::new(
            bob,
            OrderType::Limit {
                price: 100,
                amount: 30,
                side: Side::Sell,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1001,
        ));
        book.insert_order(Order::new(
            charlie,
            OrderType::Limit {
                price: 100,
                amount: 50,
                side: Side::Sell,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1002,
        ));

        // Dave buys 60 at 100.
        let buy = Order::new(
            dave,
            OrderType::Limit {
                price: 100,
                amount: 60,
                side: Side::Buy,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1003,
        );

        let result = MatchingEngine::match_order(&mut book, buy).unwrap();

        assert!(result.fully_filled);
        assert_eq!(result.total_filled, 60);
        assert_eq!(result.fills.len(), 3);
        // Alice fills 20 (fully consumed).
        assert_eq!(result.fills[0].amount, 20);
        assert_eq!(result.fills[0].maker, alice);
        // Bob fills 30 (fully consumed).
        assert_eq!(result.fills[1].amount, 30);
        assert_eq!(result.fills[1].maker, bob);
        // Charlie fills 10 (partial: 50 - 10 = 40 remaining).
        assert_eq!(result.fills[2].amount, 10);
        assert_eq!(result.fills[2].maker, charlie);

        // Charlie should have 40 remaining.
        assert_eq!(book.order_count(), 1);
    }

    // =========================================================================
    // SECURITY TESTS: Verified matching produces proofs
    // =========================================================================

    #[test]
    fn test_verified_matching_produces_proofs() {
        let mut book = OrderBook::new(eth_usdc_pair());
        let alice = make_cell(1);
        let bob = make_cell(2);

        // Alice places a sell at 100.
        book.insert_order(Order::new(
            alice,
            OrderType::Limit {
                price: 100,
                amount: 50,
                side: Side::Sell,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1000,
        ));

        // Bob places a buy at 100 via verified matching.
        let buy = Order::new(
            bob,
            OrderType::Limit {
                price: 100,
                amount: 50,
                side: Side::Buy,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1001,
        );

        let verified = VerifiedMatchingEngine::match_order(&mut book, buy, 1001, 0).unwrap();

        // Match should succeed.
        assert!(verified.result.fully_filled);
        assert_eq!(verified.result.total_filled, 50);

        // Proof should be produced and verified.
        assert_eq!(verified.fill_proofs.len(), 1);
        assert!(verified.fill_proofs[0].verified);

        // State commitments should differ (orders were consumed).
        assert_ne!(verified.pre_state.root, verified.post_state.root);
        assert_eq!(verified.pre_state.order_count, 1);
        assert_eq!(verified.post_state.order_count, 0);
    }

    // =========================================================================
    // SECURITY TESTS: State commitment Merkle tree
    // =========================================================================

    #[test]
    fn test_merkle_root_deterministic() {
        let mut book = OrderBook::new(eth_usdc_pair());
        let alice = make_cell(1);
        let bob = make_cell(2);

        book.insert_order(Order::new(
            alice,
            OrderType::Limit {
                price: 100,
                amount: 50,
                side: Side::Sell,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1000,
        ));
        book.insert_order(Order::new(
            bob,
            OrderType::Limit {
                price: 99,
                amount: 30,
                side: Side::Buy,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1001,
        ));

        let orders = collect_live_orders(&book);
        let root1 = compute_merkle_root(&orders);
        let root2 = compute_merkle_root(&orders);

        // Same orders => same root.
        assert_eq!(root1, root2);
        assert_ne!(root1, [0u8; 32]); // Not the empty sentinel.
    }

    #[test]
    fn test_inclusion_proof_verifies() {
        let mut book = OrderBook::new(eth_usdc_pair());
        let alice = make_cell(1);
        let bob = make_cell(2);

        let sell = Order::new(
            alice,
            OrderType::Limit {
                price: 100,
                amount: 50,
                side: Side::Sell,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1000,
        );
        let sell_id = sell.id;
        book.insert_order(sell);

        book.insert_order(Order::new(
            bob,
            OrderType::Limit {
                price: 99,
                amount: 30,
                side: Side::Buy,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1001,
        ));

        let orders = collect_live_orders(&book);
        let root = compute_merkle_root(&orders);

        // Generate proof for Alice's order.
        let proof = generate_inclusion_proof(&orders, &sell_id).unwrap();
        assert!(verify_inclusion_proof(&proof, &root));

        // Proof should fail against a different root.
        let fake_root = [0xFFu8; 32];
        assert!(!verify_inclusion_proof(&proof, &fake_root));
    }

    // =========================================================================
    // SECURITY TESTS: Commit-reveal order submission
    // =========================================================================

    #[test]
    fn test_commit_reveal_basic_flow() {
        let mut registry = CommitRevealRegistry::new();
        let alice = make_cell(1);

        let order = Order::new(
            alice,
            OrderType::Limit {
                price: 100,
                amount: 50,
                side: Side::Buy,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1000,
        );

        let secret = [0xAB; 32];
        let hash = compute_order_commitment(&order, &secret);

        // Commit at height 100.
        registry
            .commit(OrderCommitment {
                hash,
                committed_at: 100,
                trader: alice,
            })
            .unwrap();

        assert_eq!(registry.pending_count(), 1);

        // Reveal too early (height 101, window is 2 blocks).
        let reveal = OrderReveal {
            order: order.clone(),
            secret,
            commitment_hash: hash,
        };
        let result = registry.reveal(reveal.clone(), 101);
        assert!(result.is_err());

        // Reveal at correct time (height 102+).
        registry.reveal(reveal, 102).unwrap();
        assert_eq!(registry.pending_count(), 0);
        assert_eq!(registry.revealed_count(), 1);

        // Drain batch returns the order.
        let batch = registry.drain_batch();
        assert_eq!(batch.len(), 1);
        assert_eq!(batch[0].id, order.id);
    }

    #[test]
    fn test_commit_reveal_rejects_wrong_secret() {
        let mut registry = CommitRevealRegistry::new();
        let alice = make_cell(1);

        let order = Order::new(
            alice,
            OrderType::Limit {
                price: 100,
                amount: 50,
                side: Side::Buy,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1000,
        );

        let secret = [0xAB; 32];
        let hash = compute_order_commitment(&order, &secret);

        registry
            .commit(OrderCommitment {
                hash,
                committed_at: 100,
                trader: alice,
            })
            .unwrap();

        // Reveal with wrong secret.
        let wrong_secret = [0xCD; 32];
        let reveal = OrderReveal {
            order,
            secret: wrong_secret,
            commitment_hash: hash,
        };
        let result = registry.reveal(reveal, 102);
        assert!(matches!(
            result,
            Err(crate::commit_reveal::CommitRevealError::HashMismatch)
        ));
    }

    #[test]
    fn test_commit_reveal_batch_ordering() {
        let mut registry = CommitRevealRegistry::new();
        let alice = make_cell(1);
        let bob = make_cell(2);

        // Bob commits first (at height 100).
        let bob_order = Order::new(
            bob,
            OrderType::Limit {
                price: 100,
                amount: 30,
                side: Side::Buy,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1000,
        );
        let bob_secret = [0xBB; 32];
        let bob_hash = compute_order_commitment(&bob_order, &bob_secret);
        registry
            .commit(OrderCommitment {
                hash: bob_hash,
                committed_at: 100,
                trader: bob,
            })
            .unwrap();

        // Alice commits second (at height 101).
        let alice_order = Order::new(
            alice,
            OrderType::Limit {
                price: 100,
                amount: 50,
                side: Side::Buy,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1001,
        );
        let alice_secret = [0xAA; 32];
        let alice_hash = compute_order_commitment(&alice_order, &alice_secret);
        registry
            .commit(OrderCommitment {
                hash: alice_hash,
                committed_at: 101,
                trader: alice,
            })
            .unwrap();

        // Both reveal.
        registry
            .reveal(
                OrderReveal {
                    order: bob_order.clone(),
                    secret: bob_secret,
                    commitment_hash: bob_hash,
                },
                103,
            )
            .unwrap();
        registry
            .reveal(
                OrderReveal {
                    order: alice_order.clone(),
                    secret: alice_secret,
                    commitment_hash: alice_hash,
                },
                103,
            )
            .unwrap();

        // Batch should be ordered by commitment time: Bob first.
        let batch = registry.drain_batch();
        assert_eq!(batch.len(), 2);
        assert_eq!(batch[0].id, bob_order.id); // Bob committed first.
        assert_eq!(batch[1].id, alice_order.id);
    }

    // =========================================================================
    // SECURITY TESTS: Escrow-backed orders
    // =========================================================================

    #[test]
    fn test_escrow_required_for_submission() {
        let mut engine = OrderbookEngine::new(TradingPair::new("ETH", "USDC"));
        engine.current_height = 1000;
        let alice = make_cell(1);

        let order = Order::new(
            alice,
            OrderType::Limit {
                price: 100,
                amount: 50,
                side: Side::Buy,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1000,
        );

        // Submit without escrow => rejected.
        let result = engine.submit_order(order.clone());
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            crate::SubmitError::EscrowError(_)
        ));

        // Register escrow, then submit.
        let (_, escrow_record) = escrow::build_order_escrow_effect(&order, 1000);
        engine.register_escrow(escrow_record);

        let result = engine.submit_order(order);
        assert!(result.is_ok());
    }

    #[test]
    fn test_escrow_insufficient_collateral_rejected() {
        let mut registry = EscrowRegistry::new();
        let alice = make_cell(1);

        let order = Order::new(
            alice,
            OrderType::Limit {
                price: 100,
                amount: 50,
                side: Side::Buy,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1000,
        );

        // Register escrow with insufficient amount (need 5000, provide 1000).
        let escrow_id = escrow::compute_order_escrow_id(&order.id, &alice);
        registry.register(OrderEscrow {
            escrow_id,
            order_id: order.id,
            trader: alice,
            locked_amount: 1000, // Insufficient!
            created_at: 1000,
            consumed: false,
        });

        let result = registry.verify_collateral(&order);
        assert!(matches!(
            result,
            Err(escrow::EscrowError::InsufficientCollateral {
                required: 5000,
                locked: 1000
            })
        ));
    }

    // =========================================================================
    // SECURITY TESTS: Settlement releases escrows
    // =========================================================================

    #[test]
    fn test_settlement_releases_pre_locked_escrows() {
        let alice = make_cell(1);
        let bob = make_cell(2);

        let fill = crate::matching::Fill {
            taker_order_id: [0xAA; 32],
            maker_order_id: [0xBB; 32],
            price: 100,
            amount: 50,
            taker: bob,
            maker: alice,
            taker_side: Side::Buy,
        };

        let (settlement, effects) = build_settlement_effects(&fill, 1000);

        assert_eq!(settlement.total_payment, 5000);
        assert_eq!(settlement.buyer, bob);
        assert_eq!(settlement.seller, alice);

        // Should have 2 ReleaseEscrow effects (buyer's and seller's).
        assert_eq!(effects.len(), 2);
        for effect in &effects {
            match effect {
                pyana_turn::action::Effect::ReleaseEscrow { proof, .. } => {
                    assert!(proof.is_some());
                }
                _ => panic!("expected ReleaseEscrow effect, got {:?}", effect),
            }
        }
    }

    // =========================================================================
    // SECURITY TESTS: Dark pool conservation proofs
    // =========================================================================

    #[test]
    fn test_dark_pool_crossing_conservation() {
        let alice = make_cell(1);
        let bob = make_cell(2);

        let alice_params = PrivateOrderParams {
            amount: 100,
            blinding: [0xAA; 32],
        };
        let bob_params = PrivateOrderParams {
            amount: 80,
            blinding: [0xBB; 32],
        };

        let alice_sell = PrivateOrder::new(
            alice,
            Side::Sell,
            200,
            &alice_params,
            TimeInForce::GTC,
            1,
            1000,
        );
        let bob_buy =
            PrivateOrder::new(bob, Side::Buy, 200, &bob_params, TimeInForce::GTC, 1, 1001);

        // Cross at fill_amount = 80 (limited by Bob's amount).
        let fill_blinding = [0xCC; 32];
        let crossing = build_dark_pool_crossing(&bob_buy, &alice_sell, 80, &fill_blinding);

        // Verify conservation.
        assert!(verify_dark_pool_crossing(&crossing, 80, &fill_blinding));

        // Wrong fill amount fails verification.
        assert!(!verify_dark_pool_crossing(&crossing, 79, &fill_blinding));

        // Wrong blinding fails verification.
        assert!(!verify_dark_pool_crossing(&crossing, 80, &[0xDD; 32]));
    }

    #[test]
    fn test_dark_pool_payment_commitment_conservation() {
        let amount = 50u64;
        let price = 200u64;
        let blinding = [0xAA; 32];

        let payment_commitment = compute_payment_commitment(amount, &blinding, price);

        // Correct opening verifies.
        assert!(verify_payment_conservation(
            &payment_commitment,
            amount,
            &blinding,
            price
        ));

        // Wrong amount fails.
        assert!(!verify_payment_conservation(
            &payment_commitment,
            49,
            &blinding,
            price
        ));

        // Wrong price fails.
        assert!(!verify_payment_conservation(
            &payment_commitment,
            amount,
            &blinding,
            199
        ));
    }

    // =========================================================================
    // SECURITY TESTS: Full engine lifecycle with all protections
    // =========================================================================

    #[test]
    fn test_full_verified_engine_lifecycle() {
        let mut engine = OrderbookEngine::new(TradingPair::new("ETH", "USDC"));
        engine.current_height = 1000;

        let alice = make_cell(1);
        let bob = make_cell(2);

        // Alice: sell 50 ETH at 100 USDC.
        let alice_order = Order::new(
            alice,
            OrderType::Limit {
                price: 100,
                amount: 50,
                side: Side::Sell,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1000,
        );
        let (_, alice_escrow) = escrow::build_order_escrow_effect(&alice_order, 1000);
        engine.register_escrow(alice_escrow);
        engine.submit_order(alice_order.clone()).unwrap();

        // Verify Alice's order is in the state commitment.
        let commitment = engine.current_state_commitment();
        assert_eq!(commitment.order_count, 1);

        let proof = engine.prove_order_inclusion(&alice_order.id).unwrap();
        assert!(engine.verify_order_inclusion(&proof));

        // Bob: buy 50 ETH at 100 USDC (crosses the spread).
        let bob_order = Order::new(
            bob,
            OrderType::Limit {
                price: 100,
                amount: 50,
                side: Side::Buy,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1001,
        );
        let (_, bob_escrow) = escrow::build_order_escrow_effect(&bob_order, 1000);
        engine.register_escrow(bob_escrow);
        let result = engine.submit_order(bob_order).unwrap();

        // Match should succeed with proof.
        assert!(result.result.fully_filled);
        assert_eq!(result.fill_proofs.len(), 1);
        assert!(result.fill_proofs[0].verified);

        // Book should be empty now.
        assert_eq!(engine.book.order_count(), 0);

        // State commitment updated.
        let post = engine.current_state_commitment();
        assert_eq!(post.order_count, 0);
        assert_ne!(commitment.root, post.root);
    }

    // =========================================================================
    // SECURITY TESTS: Cancel with escrow refund
    // =========================================================================

    #[test]
    fn test_cancel_refunds_escrow() {
        let mut engine = OrderbookEngine::new(TradingPair::new("ETH", "USDC"));
        engine.current_height = 1000;

        let alice = make_cell(1);
        let order = Order::new(
            alice,
            OrderType::Limit {
                price: 100,
                amount: 50,
                side: Side::Sell,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1000,
        );
        let order_id = order.id;
        let (_, alice_escrow) = escrow::build_order_escrow_effect(&order, 1000);
        engine.register_escrow(alice_escrow);
        engine.submit_order(order).unwrap();

        // Cancel: should return a refund effect.
        let (cancelled, refund_effect) = engine.cancel_order(&order_id, &alice).unwrap();
        assert_eq!(cancelled.status, OrderStatus::Cancelled);
        match refund_effect {
            pyana_turn::action::Effect::RefundEscrow { escrow_id } => {
                assert_ne!(escrow_id, [0u8; 32]); // Real escrow ID.
            }
            _ => panic!("expected RefundEscrow effect"),
        }

        // Escrow is consumed (can't double-refund).
        assert_eq!(engine.escrows.active_count(), 0);
    }

    // =========================================================================
    // UPGRADE 1: Blinded queue for fair order batch processing
    // =========================================================================

    /// Helper: build a ConsumptionProof for a single-item blinded queue.
    ///
    /// With exactly one commitment in the queue the Merkle tree has one leaf,
    /// the root equals that leaf, and the sibling path is empty.
    fn make_single_item_proof(
        commitment: [u8; 32],
        secret: [u8; 32],
    ) -> pyana_storage::blinded::ConsumptionProof {
        // Nullifier derivation must match `crypto::derive_nullifier`.
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"blinded-queue-nullifier");
        hasher.update(&commitment);
        hasher.update(&secret);
        hasher.update(&0u64.to_le_bytes()); // position = 0
        let nullifier = *hasher.finalize().as_bytes();

        pyana_storage::blinded::ConsumptionProof {
            nullifier,
            membership_proof: vec![], // empty path for single-leaf tree
            commitment,
            position: 0,
        }
    }

    #[test]
    fn test_blinded_queue_commit_and_consume_succeeds() {
        use crate::blinded_queue::{OrderBlindedQueue, compute_blinded_order_commitment};

        let alice = make_cell(1);
        let order = Order::new(
            alice,
            OrderType::Limit {
                price: 100,
                amount: 50,
                side: Side::Buy,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1000,
        );
        let secret = [0xAB; 32];

        let mut queue = OrderBlindedQueue::new(16);

        // Commit phase: compute and submit the commitment.
        let commitment = compute_blinded_order_commitment(&order, &secret);
        let root = queue.commit(commitment).unwrap();
        assert_ne!(root, [0u8; 32]);
        assert_eq!(queue.pending_count(), 0); // not yet consumed

        // Consume phase: provide the proof with the order opening.
        let proof = make_single_item_proof(commitment, secret);
        queue.consume(order.clone(), secret, proof).unwrap();

        // The order should now be in the pending batch.
        assert_eq!(queue.pending_count(), 1);
        assert_eq!(queue.consumed_count(), 1);

        // Drain the batch and confirm the order is there.
        let batch = queue.drain_batch();
        assert_eq!(batch.len(), 1);
        assert_eq!(batch[0].id, order.id);
        assert_eq!(queue.pending_count(), 0);
    }

    #[test]
    fn test_blinded_queue_double_consume_rejected() {
        use crate::blinded_queue::{BlindedOrderError, OrderBlindedQueue, compute_blinded_order_commitment};

        let alice = make_cell(1);
        let order = Order::new(
            alice,
            OrderType::Limit {
                price: 100,
                amount: 50,
                side: Side::Buy,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1000,
        );
        let secret = [0xCD; 32];

        let mut queue = OrderBlindedQueue::new(16);
        let commitment = compute_blinded_order_commitment(&order, &secret);
        queue.commit(commitment).unwrap();

        let proof1 = make_single_item_proof(commitment, secret);
        let proof2 = make_single_item_proof(commitment, secret);

        // First consume: succeeds.
        queue.consume(order.clone(), secret, proof1).unwrap();

        // Second consume with the same nullifier: must be rejected.
        let result = queue.consume(order.clone(), secret, proof2);
        assert_eq!(result, Err(BlindedOrderError::AlreadyConsumed));

        // Only one order should be pending.
        assert_eq!(queue.pending_count(), 1);
    }

    #[test]
    fn test_blinded_queue_wrong_commitment_rejected() {
        use crate::blinded_queue::{BlindedOrderError, OrderBlindedQueue, compute_blinded_order_commitment};

        let alice = make_cell(1);
        let order = Order::new(
            alice,
            OrderType::Limit {
                price: 100,
                amount: 50,
                side: Side::Buy,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1000,
        );
        let secret = [0xEF; 32];
        let wrong_secret = [0x00; 32];

        let mut queue = OrderBlindedQueue::new(16);
        let commitment = compute_blinded_order_commitment(&order, &secret);
        queue.commit(commitment).unwrap();

        // Build proof with wrong_secret — commitment hash will not match.
        let wrong_commitment = compute_blinded_order_commitment(&order, &wrong_secret);
        // The proof's commitment field won't match what's in the queue.
        let proof = make_single_item_proof(wrong_commitment, wrong_secret);

        let result = queue.consume(order.clone(), wrong_secret, proof);
        // Either CommitmentMismatch or InvalidMembershipProof — both are acceptable rejections.
        assert!(result.is_err());
    }

    // =========================================================================
    // UPGRADE 2: Ring trade participation for cross-pair settlement
    // =========================================================================

    #[test]
    fn test_ring_trade_exchange_offers_nonempty() {
        use crate::ring_trade::OrderbookRingParticipant;
        use pyana_app_framework::ring_trade::RingTradeParticipant;

        let mut book = OrderBook::new(eth_usdc_pair());
        let alice = make_cell(1);
        let bob = make_cell(2);

        // Alice sells 50 ETH at 3000 USDC.
        book.insert_order(Order::new(
            alice,
            OrderType::Limit {
                price: 3000,
                amount: 50,
                side: Side::Sell,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1000,
        ));

        // Bob bids 30 ETH at 2900 USDC.
        book.insert_order(Order::new(
            bob,
            OrderType::Limit {
                price: 2900,
                amount: 30,
                side: Side::Buy,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1001,
        ));

        let participant = OrderbookRingParticipant::new("ETH", "USDC", &mut book);
        let offers = participant.exchange_offers();

        // Both resting orders should be exposed as exchange specs.
        assert_eq!(offers.len(), 2);
    }

    #[test]
    fn test_ring_trade_settle_leg_fills_order() {
        use crate::ring_trade::{OrderbookRingParticipant, base_asset_id};
        use pyana_app_framework::ring_trade::RingTradeParticipant;
        use pyana_intent::CommitmentId;
        use pyana_app_framework::ring_trade::Settlement;

        let mut book = OrderBook::new(eth_usdc_pair());
        let alice = make_cell(1);

        // Alice sells 50 ETH at 3000 USDC.
        book.insert_order(Order::new(
            alice,
            OrderType::Limit {
                price: 3000,
                amount: 50,
                side: Side::Sell,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1000,
        ));

        assert_eq!(book.order_count(), 1);

        let settlement = Settlement {
            from: CommitmentId([0x01; 32]),
            to: CommitmentId([0x02; 32]),
            asset: base_asset_id("ETH"), // base asset
            amount: 50,
        };

        // Scope participant so borrow is released before the final assertion.
        {
            let mut participant = OrderbookRingParticipant::new("ETH", "USDC", &mut book);
            // Solver says: fill 50 ETH from this book leg.
            participant.settle_leg(&settlement).unwrap();
        }

        // The order should now be consumed (removed from book, fully filled).
        assert_eq!(book.order_count(), 0);
    }

    #[test]
    fn test_ring_trade_rollback_leg_restores_order() {
        use crate::ring_trade::{OrderbookRingParticipant, base_asset_id};
        use pyana_app_framework::ring_trade::RingTradeParticipant;
        use pyana_intent::CommitmentId;
        use pyana_app_framework::ring_trade::Settlement;

        let mut book = OrderBook::new(eth_usdc_pair());
        let alice = make_cell(1);

        // Alice sells 50 ETH at 3000 USDC.
        let sell_order = Order::new(
            alice,
            OrderType::Limit {
                price: 3000,
                amount: 50,
                side: Side::Sell,
                time_in_force: TimeInForce::GTC,
            },
            1,
            1000,
        );
        book.insert_order(sell_order.clone());

        let settlement = Settlement {
            from: CommitmentId([0x01; 32]),
            to: CommitmentId([0x02; 32]),
            asset: base_asset_id("ETH"),
            amount: 30, // partial fill
        };

        // Scope the participant so the mutable borrow is released before we inspect.
        {
            let mut participant = OrderbookRingParticipant::new("ETH", "USDC", &mut book);

            // Settle: consume 30 out of 50.
            participant.settle_leg(&settlement).unwrap();

            // A downstream leg fails — roll back.
            participant.rollback_leg(&settlement).unwrap();
        } // participant dropped here; mutable borrow released

        // The order should be restored to 50.
        let restored = book.get_order(&sell_order.id).unwrap();
        assert_eq!(restored.remaining_amount, 50);
        assert_eq!(book.order_count(), 1);
    }
}
