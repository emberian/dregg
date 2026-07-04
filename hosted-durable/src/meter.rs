//! `meter` — the hosting-substrate meter type.
//!
//! Metering appears at several layers of the product (the durable workflow's
//! per-step tick, the object store's pay-per-operation charges, the hosting
//! meter). This module is the shared vocabulary they all charge through, so a
//! budget is one shape everywhere:
//!
//! - [`Account`] — a funded budget a holder's operations are charged against.
//!   Charges are atomic; a charge the remaining budget cannot cover is refused
//!   ([`OverBudget`]) *before* any state commits, and the balance never goes
//!   negative. the hosting storage layer consumes this type for its bucket-operation
//!   metering (its `Pricing` rate card stays domain-local, like billing's
//!   `RateCard`); the durable layer's own budget ceiling
//!   (the operated compute tier's budget gate) gates in the orchestration
//!   before a tick is scheduled.
//! - [`tally_add`] / [`tally_get`] — the process-global observability ledger:
//!   per-`(holder, key)` counters recording what actually ran/charged, readable
//!   by callers and tests without re-reading the durable store. The crate's
//!   [`metrics`](crate::metrics) module is a thin view over this ledger.
//!
//! The remaining parallel meter is `dregg-agent`'s (consumed by
//! the sandbox executor) — an upstream seam, not unified here.

use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};

/// A funded account a holder's operations are metered against — the in-process
/// form of a funded dregg `execution-lease` budget. Charges are atomic and the
/// remaining balance never goes negative (an over-budget charge is rejected,
/// not clamped).
pub struct Account {
    /// The account holder (for receipts/audit).
    pub holder: String,
    /// Remaining budget, in meter units. Decremented on each successful charge.
    remaining: Mutex<i64>,
    /// Total charged so far (for receipts/audit).
    spent: Mutex<i64>,
}

impl Account {
    /// A funded account for `holder` with `budget_units` of budget.
    pub fn funded(holder: impl Into<String>, budget_units: i64) -> Account {
        Account {
            holder: holder.into(),
            remaining: Mutex::new(budget_units.max(0)),
            spent: Mutex::new(0),
        }
    }

    /// The remaining budget.
    pub fn remaining(&self) -> i64 {
        *self.remaining.lock().expect("account poisoned")
    }

    /// The total charged so far.
    pub fn spent(&self) -> i64 {
        *self.spent.lock().expect("account poisoned")
    }

    /// Charge `units` against the account. Succeeds (returning the new remaining
    /// balance) only if the account can cover the full charge; otherwise the
    /// account is untouched and [`OverBudget`] is returned — the caller must
    /// refuse the operation before committing any state.
    pub fn charge(&self, units: i64) -> Result<i64, OverBudget> {
        let units = units.max(0);
        let mut remaining = self.remaining.lock().expect("account poisoned");
        if *remaining < units {
            return Err(OverBudget {
                requested: units,
                remaining: *remaining,
            });
        }
        *remaining -= units;
        *self.spent.lock().expect("account poisoned") += units;
        Ok(*remaining)
    }
}

/// An operation was refused because the account could not cover its metered cost.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OverBudget {
    /// The units the operation required.
    pub requested: i64,
    /// The units the account had remaining.
    pub remaining: i64,
}

impl std::fmt::Display for OverBudget {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "operation requires {} units but only {} remain",
            self.requested, self.remaining
        )
    }
}

impl std::error::Error for OverBudget {}

// ---------------------------------------------------------------------------
// The process-global observability tally.
// ---------------------------------------------------------------------------

fn ledger() -> &'static Mutex<HashMap<(String, String), i64>> {
    static LEDGER: OnceLock<Mutex<HashMap<(String, String), i64>>> = OnceLock::new();
    LEDGER.get_or_init(|| Mutex::new(HashMap::new()))
}

/// Add `delta` to the `(holder, key)` counter, returning the new value. The
/// per-instance observability ledger the durable activities record real
/// executions and charges into.
pub fn tally_add(holder: &str, key: &str, delta: i64) -> i64 {
    let mut g = ledger().lock().expect("meter tally poisoned");
    let e = g.entry((holder.to_string(), key.to_string())).or_insert(0);
    *e += delta;
    *e
}

/// Read the `(holder, key)` counter (`0` if never touched).
pub fn tally_get(holder: &str, key: &str) -> i64 {
    let g = ledger().lock().expect("meter tally poisoned");
    *g.get(&(holder.to_string(), key.to_string())).unwrap_or(&0)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn account_charges_and_refuses_over_budget() {
        let acct = Account::funded("agent:ember", 25);
        assert_eq!(acct.charge(10).unwrap(), 15);
        assert_eq!(acct.charge(10).unwrap(), 5);
        // The next 10 won't fit: refused, account untouched.
        assert_eq!(
            acct.charge(10),
            Err(OverBudget {
                requested: 10,
                remaining: 5
            })
        );
        assert_eq!(acct.remaining(), 5);
        assert_eq!(acct.spent(), 20);
        // A charge that fits still works.
        assert_eq!(acct.charge(5).unwrap(), 0);
    }

    #[test]
    fn tally_accumulates_per_holder_and_key() {
        assert_eq!(tally_get("meter-test-holder", "k"), 0);
        assert_eq!(tally_add("meter-test-holder", "k", 3), 3);
        assert_eq!(tally_add("meter-test-holder", "k", 4), 7);
        assert_eq!(tally_get("meter-test-holder", "k"), 7);
        // Distinct keys and holders never alias.
        assert_eq!(tally_get("meter-test-holder", "other"), 0);
        assert_eq!(tally_get("meter-test-holder-2", "k"), 0);
    }
}
