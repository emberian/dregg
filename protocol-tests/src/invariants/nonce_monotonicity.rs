//! Nonce monotonicity invariant.
//!
//! > Every successful turn increments the cell's nonce by exactly 1. Replay
//! > protection.
//!
//! Operationally: we apply a random number of no-op turns from a single
//! agent, recording the agent's nonce after each committed turn. The
//! observed sequence must be `0, 1, 2, ..., k` with no gaps and no
//! repeats. We also check that submitting a turn with the wrong nonce is
//! rejected and the on-ledger nonce is unchanged.

use crate::Invariant;

use proptest::prelude::*;

/// Marker for documentation / future tooling.
pub struct NonceMonotonicity;

impl Invariant for NonceMonotonicity {
    const NAME: &'static str = "nonce_monotonicity";
    const DESCRIPTION: &'static str =
        "after k committed turns, the agent's nonce is exactly k; replay (wrong nonce) is rejected";
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// Across k no-op turns, the agent's nonce should walk `0 -> 1 -> ... -> k`.
    #[test]
    fn nonce_increments_by_exactly_one(k in 1usize..30) {
        let spec = LedgerSpec {
            n_cells: 1,
            balance_each: 1_000_000,
            wide_open: true,
        };
        let (mut ledger, ids) = build_open_ledger(&spec);
        let agent = ids[0];
        let executor = TurnExecutor::new(ComputronCosts::zero());
        let mut prev_receipt_hash: Option<[u8; 32]> = None;

        for expected_pre_nonce in 0u64..(k as u64) {
            // The on-ledger nonce must match what we expect to submit.
            let actual_nonce = ledger.get(&agent).unwrap().state.nonce();
            prop_assert_eq!(
                actual_nonce,
                expected_pre_nonce,
                "agent nonce diverged before turn {}",
                expected_pre_nonce,
            );

            let turn = build_no_op_turn(agent, actual_nonce, prev_receipt_hash);
            let result = executor.execute(&turn, &mut ledger);
            prop_assert!(
                result.is_committed(),
                "expected commit at nonce {}, got {:?}",
                expected_pre_nonce,
                result,
            );

            // Thread the receipt chain forward so the next turn passes the
            // executor's ReceiptChainMismatch enforcement.
            if let dregg_turn::TurnResult::Committed { ref receipt, .. } = result {
                prev_receipt_hash = Some(receipt.receipt_hash());
            }

            let post_nonce = ledger.get(&agent).unwrap().state.nonce();
            prop_assert_eq!(
                post_nonce,
                expected_pre_nonce + 1,
                "nonce did not increment by exactly 1 (was {}, became {})",
                expected_pre_nonce,
                post_nonce,
            );
        }
    }

    /// Submitting a turn with a stale nonce must be rejected, and the
    /// ledger's stored nonce must not regress.
    #[test]
    fn stale_nonce_is_rejected_and_ledger_unchanged(skew in 1u64..10) {
        let spec = LedgerSpec {
            n_cells: 1,
            balance_each: 1_000_000,
            wide_open: true,
        };
        let (mut ledger, ids) = build_open_ledger(&spec);
        let agent = ids[0];
        let executor = TurnExecutor::new(ComputronCosts::zero());

        // Advance the agent's nonce to some non-zero value, threading the
        // receipt chain so each successive turn passes the executor's
        // ReceiptChainMismatch enforcement.
        let mut prev_receipt_hash: Option<[u8; 32]> = None;
        for _ in 0..5 {
            let n = ledger.get(&agent).unwrap().state.nonce();
            let turn = build_no_op_turn(agent, n, prev_receipt_hash);
            let res = executor.execute(&turn, &mut ledger);
            prop_assert!(res.is_committed());
            if let dregg_turn::TurnResult::Committed { ref receipt, .. } = res {
                prev_receipt_hash = Some(receipt.receipt_hash());
            }
        }
        let nonce_before = ledger.get(&agent).unwrap().state.nonce();
        prop_assert_eq!(nonce_before, 5);

        // Submit a turn with a nonce that's `skew` behind current. This is a
        // replay scenario and must be rejected. We use saturating_sub so we
        // never underflow — `skew <= nonce_before` for `skew in 1..10` and
        // `nonce_before = 5`, so some inputs will hit nonce=0 and others
        // will hit negative-difference cases. Both must reject.
        let stale_nonce = nonce_before.saturating_sub(skew);
        // If skew==0 we'd be submitting at the current nonce which would
        // legitimately succeed; the strategy excludes that.
        prop_assume!(stale_nonce < nonce_before);

        // Stale nonce: pass the current prev_receipt_hash so the rejection
        // is driven by nonce mismatch, not ReceiptChainMismatch.
        let turn = build_no_op_turn(agent, stale_nonce, prev_receipt_hash);
        let result = executor.execute(&turn, &mut ledger);
        prop_assert!(
            matches!(result, TurnResult::Rejected { .. }),
            "stale-nonce turn should be rejected, got {:?}",
            result,
        );

        // Ledger nonce must not have regressed.
        let nonce_after = ledger.get(&agent).unwrap().state.nonce();
        prop_assert_eq!(
            nonce_after,
            nonce_before,
            "rejected turn must not move the nonce",
        );
    }
}
