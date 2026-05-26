//! Receipt chain causal soundness invariant.
//!
//! > Every turn's `previous_receipt_hash` matches the agent's prior
//! > receipt; the chain is a total order per-agent.
//!
//! Operationally: build a chain of `k` no-op turns from a single agent,
//! each carrying the previous receipt's hash. Then:
//!
//! - `verify_receipt_chain` must accept the chain.
//! - Each receipt's `pre_state_hash` must equal the previous receipt's
//!   `post_state_hash` (state continuity).
//! - Each receipt's `previous_receipt_hash` field must equal the previous
//!   receipt's `receipt_hash()` (causal continuity).
//! - Removing or swapping any non-endpoint receipt must break verification.

use crate::Invariant;
use crate::generators::build_no_op_turn;

use dregg_turn::{TurnExecutor, TurnReceipt, TurnResult};
use proptest::prelude::*;

pub struct ReceiptChain;

impl Invariant for ReceiptChain {
    const NAME: &'static str = "receipt_chain";
    const DESCRIPTION: &'static str = "per-agent receipts form a hash-linked total order; verify_receipt_chain accepts iff the chain is intact";
}

/// Build a chain of `n` committed no-op turns for `agent`.
fn build_chain(
    executor: &TurnExecutor,
    ledger: &mut dregg_cell::Ledger,
    agent: dregg_cell::CellId,
    n: usize,
) -> Vec<TurnReceipt> {
    let mut chain = Vec::with_capacity(n);
    for _ in 0..n {
        let nonce = ledger.get(&agent).unwrap().state.nonce();
        let prev = chain.last().map(|r: &TurnReceipt| r.receipt_hash());
        let turn = build_no_op_turn(agent, nonce, prev);
        match executor.execute(&turn, ledger) {
            TurnResult::Committed { receipt, .. } => chain.push(receipt),
            other => panic!("expected commit, got {:?}", other),
        }
    }
    chain
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// A correctly constructed chain verifies; pre/post state hashes link;
    /// previous_receipt_hash fields link.
    #[test]
    fn correctly_built_chain_verifies(chain_len in 2usize..15) {
        let spec = LedgerSpec {
            n_cells: 1,
            balance_each: 100_000,
            wide_open: true,
        };
        let (mut ledger, ids) = build_open_ledger(&spec);
        let agent = ids[0];
        let executor = TurnExecutor::new(ComputronCosts::zero());

        let chain = build_chain(&executor, &mut ledger, agent, chain_len);

        // Whole-chain verification.
        prop_assert!(
            verify_receipt_chain(&chain).is_ok(),
            "verify_receipt_chain rejected a chain we built ourselves",
        );

        // Pairwise: state hashes link.
        for i in 1..chain.len() {
            prop_assert_eq!(
                chain[i].pre_state_hash,
                chain[i - 1].post_state_hash,
                "pre/post state-hash link broke at index {}",
                i,
            );
        }

        // Pairwise: previous_receipt_hash links.
        prop_assert!(chain[0].previous_receipt_hash.is_none(),
            "genesis receipt must have previous_receipt_hash = None");
        for i in 1..chain.len() {
            let expected = chain[i - 1].receipt_hash();
            prop_assert_eq!(
                chain[i].previous_receipt_hash,
                Some(expected),
                "previous_receipt_hash link broke at index {}",
                i,
            );
        }
    }

    /// Removing any non-endpoint receipt from the chain must break
    /// verification — this is what causal soundness BUYS us.
    #[test]
    fn removing_a_receipt_breaks_verification(chain_len in 3usize..10) {
        let spec = LedgerSpec {
            n_cells: 1,
            balance_each: 100_000,
            wide_open: true,
        };
        let (mut ledger, ids) = build_open_ledger(&spec);
        let agent = ids[0];
        let executor = TurnExecutor::new(ComputronCosts::zero());
        let chain = build_chain(&executor, &mut ledger, agent, chain_len);

        for remove_idx in 1..(chain.len() - 1) {
            let mut broken = chain.clone();
            broken.remove(remove_idx);
            prop_assert!(
                verify_receipt_chain(&broken).is_err(),
                "removing receipt at index {} should have broken verification",
                remove_idx,
            );
        }
    }

    /// Swapping two adjacent receipts must also break verification.
    #[test]
    fn swapping_adjacent_receipts_breaks_verification(chain_len in 3usize..10) {
        let spec = LedgerSpec {
            n_cells: 1,
            balance_each: 100_000,
            wide_open: true,
        };
        let (mut ledger, ids) = build_open_ledger(&spec);
        let agent = ids[0];
        let executor = TurnExecutor::new(ComputronCosts::zero());
        let chain = build_chain(&executor, &mut ledger, agent, chain_len);

        let mut swapped = chain.clone();
        swapped.swap(1, 2);
        prop_assert!(
            verify_receipt_chain(&swapped).is_err(),
            "swapping adjacent receipts should have broken verification",
        );
    }
}
