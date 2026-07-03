//! **The recurring half** — a recurring billing charge on the proven standing-obligation
//! capacity ([`dregg_cell::obligation_standing`], `cell/src/obligation_standing.rs`).
//!
//! ## A recurring charge IS a standing obligation — no new primitive
//!
//! Usage billing (the [`crate::invoice`] side) aggregates *variable* settled charges after
//! the fact. The other half of a real billing plane is the *recurring* charge: a fixed
//! base fee an account owes every period — a plan fee, a seat, a floor. That is exactly a
//! [`StandingObligation`](dregg_cell::obligation_standing): the schedule (amount, period,
//! start, beneficiary) is committed into the cell, a period is discharged ONCE, on
//! schedule, for the exact amount (the recurring forge-detectors bite — no early / double /
//! over / under discharge), and a missed period LAPSES (the audit tooth). This module is a
//! thin, honest NAMING of that proven capacity in billing vocabulary: a [`RecurringPlan`]
//! *is* an `ObligationTerms`, `bill_period` *is* `discharge`, and `is_lapsed` *is* the
//! obligation `audit`. It follows the same shape the sibling `starbridge-subscription`
//! crate's `obligation.rs` uses. The per-period value move is a real conserved
//! [`dregg_app_framework::Effect::Transfer`].

use dregg_app_framework::Effect;
use dregg_cell::Cell;
use dregg_cell::obligation_standing::{
    Discharge, ObligationError, ObligationState, ObligationTerms, discharge, is_obligation,
    open_obligation,
};
use dregg_types::CellId;

/// A recurring billing **plan** — the fixed periodic charge, expressed directly as the
/// proven [`ObligationTerms`]. A plan says: the `account` owes `fee` of `asset` to the
/// `provider` every `period_blocks`, starting at `first_due_block`, for `term_periods`
/// periods (`0` = perpetual / until cancelled).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecurringPlan {
    /// The account — who is charged each period (the obligation's `obligor`).
    pub account: CellId,
    /// The provider — who is paid each period (the obligation's `beneficiary`).
    pub provider: CellId,
    /// The asset each period is denominated in.
    pub asset: CellId,
    /// The fee charged each period. Must be `> 0`.
    pub fee: i64,
    /// The period length in blocks — the stride of the temporal cursor. Must be `> 0`.
    pub period_blocks: i64,
    /// The block at which the first period falls due (the obligation `start`).
    pub first_due_block: i64,
    /// The bounded number of periods, or `0` for a perpetual plan.
    pub term_periods: i64,
}

impl RecurringPlan {
    /// A recurring plan: `account` owes `fee` of `asset` to `provider` every
    /// `period_blocks`, first due at `first_due_block`, for `term_periods` (`0` =
    /// perpetual).
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        account: CellId,
        provider: CellId,
        asset: CellId,
        fee: i64,
        period_blocks: i64,
        first_due_block: i64,
        term_periods: i64,
    ) -> Self {
        RecurringPlan {
            account,
            provider,
            asset,
            fee,
            period_blocks,
            first_due_block,
            term_periods,
        }
    }

    /// The proven [`ObligationTerms`] this plan seals — the identity map into the capacity.
    pub fn terms(&self) -> ObligationTerms {
        ObligationTerms::new(
            self.account,
            self.provider,
            self.asset,
            self.fee,
            self.period_blocks,
            self.first_due_block,
            self.term_periods,
        )
    }

    /// Whether the plan is well-formed (positive fee + period).
    pub fn is_well_formed(&self) -> bool {
        self.terms().is_well_formed()
    }
}

/// Why a recurring billing operation was refused. Wraps the proven capacity's
/// [`ObligationError`] so callers see the exact forge/skip rejection.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RecurringError {
    /// The plan is ill-formed (non-positive fee or period).
    IllFormedPlan,
    /// A proven-capacity rejection: early charge, double charge, wrong amount, completed
    /// term, or behind schedule.
    Obligation(ObligationError),
}

impl std::fmt::Display for RecurringError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RecurringError::IllFormedPlan => write!(f, "recurring plan is not well-formed"),
            RecurringError::Obligation(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for RecurringError {}

/// A live **recurring bill** — a [`dregg_cell::Cell`] carrying the proven standing
/// obligation, plus the [`RecurringPlan`] it was opened under. Every state-changing method
/// routes through the proven capacity ([`open_obligation`] / [`discharge`] /
/// [`ObligationState::audit`]).
#[derive(Clone, Debug)]
pub struct RecurringBill {
    /// The contract cell carrying the committed obligation ledger.
    pub cell: Cell,
    /// The plan in force.
    pub plan: RecurringPlan,
}

impl RecurringBill {
    /// **Open** a recurring bill on a fresh cell under `plan`. Seals the plan's terms digest
    /// and initializes the temporal cursor to the first due block, with zero periods
    /// billed. Rejects an ill-formed plan.
    pub fn open(plan: RecurringPlan) -> Result<RecurringBill, RecurringError> {
        if !plan.is_well_formed() {
            return Err(RecurringError::IllFormedPlan);
        }
        let mut cell = Cell::with_balance(*plan.account.as_bytes(), *plan.asset.as_bytes(), 0);
        open_obligation(&mut cell, &plan.terms()).map_err(RecurringError::Obligation)?;
        Ok(RecurringBill { cell, plan })
    }

    /// Whether this cell genuinely carries a standing obligation.
    pub fn is_obligation(&self) -> bool {
        is_obligation(&self.cell)
    }

    /// The period index the committed cursor currently expects — derived from the committed
    /// `next_due`, not trusted from any input.
    pub fn expected_period(&self) -> i64 {
        let state =
            ObligationState::read(&self.cell).expect("recurring bill carries an obligation");
        (state.next_due - self.plan.first_due_block) / self.plan.period_blocks
    }

    /// **Bill the current period** at schedule clock `clock` — discharge the obligation.
    /// Routes entirely through the proven [`discharge`]: the cursor must have reached this
    /// period's due block (no early charge), the period must be the cursor's current one
    /// (no double charge / no skip), and the amount is exactly the plan fee. On accept the
    /// committed cursor advances strictly by one period. Returns the amount to move (the
    /// fee); [`Self::fee_transfer_effect`] turns it into the real conserved value move.
    /// Nothing is mutated on a rejection (the proven capacity is fail-closed).
    pub fn bill_period(&mut self, clock: i64) -> Result<i64, RecurringError> {
        let step = Discharge {
            period_index: self.expected_period(),
            amount: self.plan.fee,
            clock,
        };
        discharge(&mut self.cell, &self.plan.terms(), &step).map_err(RecurringError::Obligation)
    }

    /// The **real value move** of one period — the conserved kernel
    /// [`Effect::Transfer`](dregg_app_framework::Effect) of the plan fee from the account to
    /// the provider (the same effect the [`Payable`](dregg_app_framework::Payable) DSI
    /// desugars to). Pair it with [`Self::bill_period`]: the schedule is enforced by the
    /// proven obligation, the value by the conserved transfer.
    pub fn fee_transfer_effect(&self) -> Effect {
        Effect::Transfer {
            from: self.plan.account,
            to: self.plan.provider,
            amount: self.plan.fee.max(0) as u64,
        }
    }

    /// How many periods have been billed (the committed discharged count).
    pub fn periods_billed(&self) -> i64 {
        ObligationState::read(&self.cell)
            .map(|s| s.discharged_count)
            .unwrap_or(0)
    }

    /// Whether the recurring bill is **lapsed** at `clock` — a due period went unbilled. The
    /// proven `audit` tooth: an account whose committed billed-count is behind the number of
    /// periods the schedule demands by `clock` is detectably behind.
    pub fn is_lapsed(&self, clock: i64) -> bool {
        let state =
            ObligationState::read(&self.cell).expect("recurring bill carries an obligation");
        matches!(
            state.audit(&self.plan.terms(), clock),
            Err(ObligationError::BehindSchedule { .. })
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cid(n: u8) -> CellId {
        CellId::from_bytes([n; 32])
    }

    /// Account 1 owes a 50 base fee of asset 9 to provider 2 every 100 blocks from 1000.
    fn sample_plan() -> RecurringPlan {
        RecurringPlan::new(cid(1), cid(2), cid(9), 50, 100, 1000, 0)
    }

    // ── the temporal cursor + per-period discharge (the proven core) ──
    #[test]
    fn open_then_bill_advances_the_temporal_cursor() {
        let mut bill = RecurringBill::open(sample_plan()).unwrap();
        assert!(bill.is_obligation());
        assert_eq!(bill.expected_period(), 0);

        // Bill period 0, due at 1000, at clock 1000.
        assert_eq!(bill.bill_period(1000), Ok(50), "on-schedule charge accepts");
        assert_eq!(bill.periods_billed(), 1);
        assert_eq!(bill.expected_period(), 1);
        // Bill period 1, due at 1100.
        assert_eq!(bill.bill_period(1100), Ok(50));
        assert_eq!(bill.periods_billed(), 2);
    }

    // ── the temporal cursor is ENFORCED: an early charge is refused ──
    #[test]
    fn early_charge_is_rejected() {
        let mut bill = RecurringBill::open(sample_plan()).unwrap();
        assert_eq!(
            bill.bill_period(999),
            Err(RecurringError::Obligation(ObligationError::NotYetDue {
                due_block: 1000,
                clock: 999,
            }))
        );
        assert_eq!(bill.periods_billed(), 0);
        assert_eq!(
            bill.bill_period(1000),
            Ok(50),
            "the same period charges once due"
        );
    }

    // ── a missed period LAPSES (the proven audit tooth) ──
    #[test]
    fn missed_period_lapses() {
        let mut behind = RecurringBill::open(sample_plan()).unwrap();
        behind.bill_period(1000).unwrap(); // only period 0.
        // By 1250 the schedule demands 3 periods (0@1000, 1@1100, 2@1200).
        assert!(
            behind.is_lapsed(1250),
            "an account behind schedule is lapsed"
        );

        let mut current = RecurringBill::open(sample_plan()).unwrap();
        current.bill_period(1000).unwrap();
        current.bill_period(1100).unwrap();
        current.bill_period(1200).unwrap();
        assert!(
            !current.is_lapsed(1250),
            "an on-schedule account is not lapsed"
        );
    }

    // ── the value move is a real conserved Transfer ──
    #[test]
    fn fee_transfer_is_a_conserved_transfer() {
        let bill = RecurringBill::open(sample_plan()).unwrap();
        match bill.fee_transfer_effect() {
            Effect::Transfer { from, to, amount } => {
                assert_eq!(from, cid(1));
                assert_eq!(to, cid(2));
                assert_eq!(amount, 50);
            }
            other => panic!("expected Effect::Transfer, got {other:?}"),
        }
    }

    #[test]
    fn an_illformed_plan_is_rejected() {
        let bad = RecurringPlan::new(cid(1), cid(2), cid(9), 0, 100, 1000, 0);
        assert_eq!(
            RecurringBill::open(bad).err(),
            Some(RecurringError::IllFormedPlan)
        );
    }
}
