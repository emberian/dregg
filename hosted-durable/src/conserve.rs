//! `conserve` — the conserving-move primitive the settlement rail upholds,
//! computed by the substrate's proven signed-balance discipline.
//!
//! The settlement's conserving move — debit the payer by `amount`, credit the
//! beneficiary by the same `amount`, so the per-asset Σδ = 0 — is the kernel
//! `Effect::Transfer` paired-delta law:
//!
//! - Lean: `metatheory/Dregg2/Exec/RecordKernel.lean` `recTransfer_balanceSum_conserve`
//!   — a transfer between two distinct accounts preserves the total `balance`
//!   field (debit and credit cancel) — and the apex
//!   `metatheory/Dregg2/AssuranceCase.lean` `conservation_guarantee`.
//! - Rust home of that `recTransfer` debit/credit: `dregg_cell::CellState`'s
//!   signed-balance epoch — [`CellState::debit_balance`] (refuse-below-zero, the
//!   `InsufficientFunds` floor) + [`CellState::credit_balance`]
//!   (overflow-checked). `turn/src/action.rs` classifies `Effect::Transfer` as
//!   `LinearityClass::Conservative` (paired-delta), the executor-level shadow of
//!   the same theorem.
//!
//! [`apply_conserving_transfer`] runs the move through `dregg_cell::CellState`
//! on every build — the deployed Rust home of the proven theorem, not an operated-layer
//! re-derivation. (This used to be a `dregg-conserve` feature lane with a
//! hand-rolled `i64` mirror as the default; the mirror survives only as a
//! `#[cfg(test)]` cross-check that the substrate move equals the plain
//! paired-delta integers.)
//!
//! Scope of what this primitive guarantees: it is the conserving-move *witness*.
//! The authoritative conservation on the shipped settlement paths is the node's
//! on-chain `Σδ = 0` (one signed `Effect::Transfer`), re-validated by the
//! pg-dregg chain tooth — not this local arithmetic. `TestConservingLedger`
//! drives `apply_conserving_transfer` directly; the node-API and Payable rails
//! delegate the move to the node, and `verified.rs` computes the receipt-witness
//! balances as guarded paired-delta integers (debit refuses-below-zero, credit
//! is overflow-checked), consistent with this primitive.
//!
//! [`CellState::debit_balance`]: https://docs.rs/dregg-cell
//! [`CellState::credit_balance`]: https://docs.rs/dregg-cell

use dregg_cell::CellState;

use crate::settle::SettleError;

/// The post-balances of one conserving payer → beneficiary move. The invariant
/// `new_payer + new_beneficiary == payer_balance + beneficiary_balance` (per
/// asset, Σδ = 0) holds by construction of the kernel transfer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ConservedMove {
    /// The payer's balance after the debit.
    pub new_payer: i64,
    /// The beneficiary's balance after the credit.
    pub new_beneficiary: i64,
}

/// Apply a conserving transfer of `amount` of `asset` from a payer holding
/// `payer_balance` to a beneficiary holding `beneficiary_balance`, returning the
/// post-balances.
///
/// The move runs through the substrate's proven `dregg_cell::CellState`
/// signed-balance primitive (`recTransfer_balanceSum_conserve`): the payer is
/// debited *exactly* what the beneficiary is credited, so the per-asset Σδ = 0.
/// A debit that would take the payer below zero is refused
/// ([`SettleError::InsufficientFunds`]) — the `CellState::debit_balance` floor
/// (a funded lease reserves its budget, so within budget this never fires; it
/// guards against settling work the lease did not prove it paid for).
///
/// `amount` must be positive (the caller enforces [`SettleError::NonPositiveAmount`]
/// first); a non-positive or out-of-`u64`-range amount is rejected here too.
pub fn apply_conserving_transfer(
    asset: &str,
    payer: &str,
    payer_balance: i64,
    beneficiary_balance: i64,
    amount: i64,
) -> Result<ConservedMove, SettleError> {
    if amount <= 0 {
        return Err(SettleError::NonPositiveAmount(amount));
    }
    // `amount > 0` already, so this conversion is the in-range path; an
    // out-of-`u64` amount is a malformed charge, refused.
    let amt = u64::try_from(amount).map_err(|_| SettleError::NonPositiveAmount(amount))?;

    let mut payer_cell = CellState::new(payer_balance);
    // `debit_balance` refuses to go below zero. A `false` return is exactly
    // "the payer does not hold enough" (`InsufficientFunds`).
    if !payer_cell.debit_balance(amt) {
        return Err(SettleError::InsufficientFunds {
            payer: payer.to_string(),
            asset: asset.to_string(),
            balance: payer_balance,
            needed: amount,
        });
    }
    let mut beneficiary_cell = CellState::new(beneficiary_balance);
    // `credit_balance` is overflow-checked; a `false` return is an `i64`
    // overflow of the beneficiary's holdings (not a conservation fault) — the
    // backend refuses rather than wrap. Practically unreachable for metered
    // settlement, but the substrate primitive's failure mode.
    if !beneficiary_cell.credit_balance(amt) {
        return Err(SettleError::Backend(format!(
            "beneficiary balance would overflow crediting {amount} of `{asset}` from `{payer}`"
        )));
    }
    Ok(ConservedMove {
        new_payer: payer_cell.balance(),
        new_beneficiary: beneficiary_cell.balance(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn move_conserves_sum() {
        // Σδ = 0: what leaves the payer arrives at the beneficiary, exactly.
        let before = 100 + 5;
        let m = apply_conserving_transfer("USD", "lessee", 100, 5, 7).expect("move");
        assert_eq!(m.new_payer, 93);
        assert_eq!(m.new_beneficiary, 12);
        assert_eq!(m.new_payer + m.new_beneficiary, before, "Σδ = 0");
    }

    #[test]
    fn refuses_below_zero_payer() {
        // The `debit_balance` floor: a debit beyond the reserve is refused,
        // nothing moves.
        assert!(matches!(
            apply_conserving_transfer("USD", "lessee", 2, 0, 5),
            Err(SettleError::InsufficientFunds {
                balance: 2,
                needed: 5,
                ..
            })
        ));
    }

    #[test]
    fn refuses_non_positive() {
        assert!(matches!(
            apply_conserving_transfer("USD", "lessee", 100, 0, 0),
            Err(SettleError::NonPositiveAmount(0))
        ));
        assert!(matches!(
            apply_conserving_transfer("USD", "lessee", 100, 0, -3),
            Err(SettleError::NonPositiveAmount(-3))
        ));
    }

    /// Conservation holds across a sweep of substrate moves — the post-sum
    /// always equals the pre-sum.
    #[test]
    fn conserves_across_a_sweep() {
        let mut payer = 1_000i64;
        let mut benef = 0i64;
        for amount in [1, 7, 13, 100, 250, 3] {
            let pre = payer + benef;
            let m = apply_conserving_transfer("USD", "lessee", payer, benef, amount)
                .expect("in-budget move");
            payer = m.new_payer;
            benef = m.new_beneficiary;
            assert_eq!(payer + benef, pre, "every move conserves Σδ = 0");
        }
        assert_eq!(payer, 1_000 - (1 + 7 + 13 + 100 + 250 + 3));
        assert_eq!(benef, 1 + 7 + 13 + 100 + 250 + 3);
    }

    /// The demoted reference mirror: the substrate `CellState` move must equal
    /// the plain paired-delta integers (`payer - amount` / `beneficiary +
    /// amount`, refuse below zero). This was the default-build implementation
    /// before the flip; it survives only as this cross-check.
    #[test]
    fn substrate_move_equals_the_reference_paired_delta() {
        fn reference(payer: i64, benef: i64, amount: i64) -> Option<(i64, i64)> {
            if amount <= 0 || payer < amount {
                return None;
            }
            Some((payer - amount, benef.checked_add(amount)?))
        }
        for (payer, benef, amount) in [
            (100, 5, 7),
            (1, 0, 1),
            (1_000_000, 999, 250),
            (2, 0, 5),   // insufficient — both must refuse
            (100, 0, 0), // non-positive — both must refuse
        ] {
            let subst = apply_conserving_transfer("USD", "p", payer, benef, amount).ok();
            let refr = reference(payer, benef, amount);
            assert_eq!(
                subst.map(|m| (m.new_payer, m.new_beneficiary)),
                refr,
                "substrate and reference disagree at ({payer}, {benef}, {amount})"
            );
        }
    }
}
