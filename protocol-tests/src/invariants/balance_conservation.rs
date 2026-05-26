//! Balance conservation invariant.
//!
//! > For any turn that doesn't carry a sovereign-cell proof, the sum of
//! > `balance_change` across all actions plus the fee equals zero.
//!
//! Operationally: we generate a random sequence of `Transfer` turns against
//! an open ledger, execute them through `TurnExecutor`, and check that the
//! total ledger balance after all turns equals `initial_total - sum(fees)`.
//! Conservation is the dual of "no value is created or destroyed by the
//! protocol".
//!
//! The test deliberately uses fee=0 so the invariant collapses to
//! `total_after == initial_total`. Fees are tested separately in
//! `multi_asset_fees` in `teasting/`.

use crate::Invariant;

use proptest::prelude::*;

/// Marker for documentation / future tooling. The actual test lives below.
pub struct BalanceConservation;

impl Invariant for BalanceConservation {
    const NAME: &'static str = "balance_conservation";
    const DESCRIPTION: &'static str =
        "sum of all cell balances after a sequence of fee-zero turns equals the initial total";
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// For any sequence of valid transfer turns at fee=0, the total ledger
    /// balance is unchanged.
    #[test]
    fn balance_conservation_holds(ops in arb_transfer_ops(4, 500, 30)) {
        let spec = LedgerSpec {
            n_cells: 4,
            balance_each: 10_000,
            wide_open: true,
        };
        let (mut ledger, ids) = build_open_ledger(&spec);
        let initial_total: u64 = (spec.balance_each) * (spec.n_cells as u64);

        let executor = TurnExecutor::new(ComputronCosts::zero());

        for op in &ops {
            // Self-transfer ops are no-ops in the executor; skip to avoid noise.
            if op.from_idx == op.to_idx {
                continue;
            }
            let from = ids[op.from_idx];
            let to = ids[op.to_idx];
            let nonce = ledger.get(&from).unwrap().state.nonce();
            let turn = build_transfer_turn(from, to, op.amount, nonce, None);

            // Rejected turns (e.g. insufficient balance) don't violate the
            // invariant — they leave the ledger unchanged.
            let _ = executor.execute(&turn, &mut ledger);
        }

        // INVARIANT: total ledger balance is conserved.
        let current_total: u64 = ids
            .iter()
            .map(|id| ledger.get(id).unwrap().state.balance())
            .sum();
        prop_assert_eq!(
            current_total,
            initial_total,
            "balance conservation violated: initial={}, current={}",
            initial_total,
            current_total,
        );
    }
}
