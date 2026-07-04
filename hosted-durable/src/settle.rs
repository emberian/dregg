//! `settle` — the metering→**Payable** fold: turn the durable meter into a
//! conserving, exactly-once value flow (the dregg `Payable` rail, modelled).
//!
//! ## Where this sits (the three ledgers, folded into one)
//!
//! A leased durable run touches three quantities; this module is where they are
//! made coherent rather than three independent counters:
//!
//! ```text
//!   lease budget   (the RESERVE)  — `budget_units` the funded lease proves was paid in.
//!     └─ durable meter (the TICK) — each step's `MeterTick` charges `per_period_units`
//!        │                          against the reserve; an over-budget tick fails the
//!        │                          workflow BEFORE it commits (lapse → reap). The
//!        │                          per-(lease,period) charge rows are the meter outbox.
//!        └─ Payable settle (PAY)  — THIS module: each metered period is settled as one
//!                                   conserving transfer lessee → provider, EXACTLY-ONCE
//!                                   keyed by `(lease, period)`. The settled total equals
//!                                   the metered total, which is ≤ the reserve.
//! ```
//!
//! The invariant the fold upholds (and the tests prove): for any lease,
//! `Σ settled(period) == Σ metered(period) ≤ budget`, and **every transfer
//! conserves** (the payer is debited exactly what the beneficiary is credited, so
//! the per-asset Σδ = 0 — the dregg value model). Re-running a period (a crash
//! re-dispatch, a daemon re-poll) settles nothing new: the `(lease, period)` key
//! is the idempotency key, so the meter is exactly-once (duroxide replay / the pg
//! outbox `ON CONFLICT DO NOTHING`) and the settlement is exactly-once (the
//! [`Settlement`] dedup below), and the two never double-count each other.
//!
//! ## The backends behind the one [`Settlement`] seam
//!
//! - **[`crate::payable::PayableSettlement`]** — the production rail: each
//!   [`LeaseCharge`] becomes ONE conserving kernel `Effect::Transfer` turn,
//!   handed to an injected [`PaySubmitter`](crate::payable::PaySubmitter) that
//!   signs + executes it (a dregg node client — the node's verified producer
//!   runs the desugar; the in-process `dregg_payable::resolve_pay` consumption
//!   is a named residual, see [`crate::payable`]). The recorded on-chain turn
//!   hash is readable back through [`Settlement::settled_turn_hash`], which is
//!   what a sealed product receipt threads into its `turn_receipt_hash` view
//!   link.
//! - **a live-node settlement adapter** — the live-node rail: the same
//!   conserving `Transfer` submitted over the node's HTTP API, with a durable
//!   write-ahead settle ledger for cross-restart exactly-once.
//! - **[`VerifiedConservingStore`](crate::verified::VerifiedConservingStore)**
//!   (feature `pg-dregg`) — the pg-dregg-backed verified chain store.
//! - **[`TestConservingLedger`]** — the in-process test double (below). It is a
//!   `HashMap` ledger for offline tests and MUST NOT be a production default;
//!   its conserving move still runs through the substrate primitive
//!   ([`crate::conserve::apply_conserving_transfer`] → `dregg_cell::CellState`,
//!   the deployed Rust home of `recTransfer_balanceSum_conserve` /
//!   `conservation_guarantee`), so even the double conserves by the proven
//!   discipline.
//!
//! **The pg fold:** [`settle_meter_outbox`] (feature `pg`) reads the
//! [`read_meter_outbox`](crate::read_meter_outbox) rows a durable run committed
//! and settles each through a [`Settlement`] — the literal "the `Payable`
//! settlement reads the settlement outbox" path the meter docs name.

use std::collections::HashMap;
use std::sync::Mutex;

/// One period's charge to settle: move `amount` of `asset` from `payer` (the
/// lessee) to `beneficiary` (the provider that ran the work), recorded under the
/// idempotency key `(lease_id, period)`.
///
/// `lease_id` is the durable workflow instance (the same key the meter outbox is
/// keyed by), so a charge here lines up row-for-row with a meter tick.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LeaseCharge {
    /// The lessee paying for the work (the dregg lease holder).
    pub payer: String,
    /// The provider being paid (the backend that ran the durable workload).
    pub beneficiary: String,
    /// The asset the transfer is denominated in (the lease's `token_id`).
    pub asset: String,
    /// The lease / durable-instance id — half the idempotency key.
    pub lease_id: String,
    /// The 1-based period ordinal within the lease — the other half of the key.
    pub period: i64,
    /// The units to move for this period (the metered `per_period_units`).
    pub amount: i64,
}

impl LeaseCharge {
    /// A charge moving `amount` of `asset` from `payer` to `beneficiary` for
    /// `(lease_id, period)`.
    pub fn new(
        payer: impl Into<String>,
        beneficiary: impl Into<String>,
        asset: impl Into<String>,
        lease_id: impl Into<String>,
        period: i64,
        amount: i64,
    ) -> LeaseCharge {
        LeaseCharge {
            payer: payer.into(),
            beneficiary: beneficiary.into(),
            asset: asset.into(),
            lease_id: lease_id.into(),
            period,
            amount,
        }
    }
}

/// A settled transfer — the receipt of one conserving `payer → beneficiary` move.
///
/// `replayed` is `true` when the `(lease_id, period)` was already settled and this
/// call returned the recorded receipt without moving value again (the exactly-once
/// guarantee made observable).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SettleReceipt {
    pub lease_id: String,
    pub period: i64,
    pub asset: String,
    pub amount: i64,
    /// The payer's balance after the transfer (or at the time of the first settle,
    /// for a replay).
    pub payer_balance: i64,
    /// The beneficiary's balance after the transfer.
    pub beneficiary_balance: i64,
    /// `true` if this period was already settled and no value moved this call.
    pub replayed: bool,
}

/// Why a settlement failed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SettleError {
    /// The charge amount is non-positive — a settlement must move value forward.
    NonPositiveAmount(i64),
    /// The payer does not hold enough of the asset to cover the charge. A funded
    /// lease reserves its budget up front, so within budget this never fires; it
    /// guards against settling work the lease did not prove was paid for.
    InsufficientFunds {
        payer: String,
        asset: String,
        balance: i64,
        needed: i64,
    },
    /// The same `(lease_id, period)` was already settled with *different* terms
    /// (a programming error — the idempotency key must identify a unique charge).
    Conflict { lease_id: String, period: i64 },
    /// The real settlement backend (a dregg node) refused or could not execute
    /// the conserving `Transfer` turn. Carries the node's reason (an HTTP/transport
    /// fault, a rejected turn, or an unauthorized/over-budget `from` cell). Distinct
    /// from [`SettleError::InsufficientFunds`], which the in-process ledger raises
    /// before any wire call: this is the live rail saying no.
    Backend(String),
}

impl std::fmt::Display for SettleError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SettleError::NonPositiveAmount(a) => {
                write!(f, "settlement amount must be > 0, got {a}")
            }
            SettleError::InsufficientFunds {
                payer,
                asset,
                balance,
                needed,
            } => write!(
                f,
                "payer `{payer}` holds {balance} of `{asset}`, needs {needed}"
            ),
            SettleError::Conflict { lease_id, period } => write!(
                f,
                "period {period} of lease `{lease_id}` already settled with different terms"
            ),
            SettleError::Backend(why) => write!(f, "settlement backend refused: {why}"),
        }
    }
}

impl std::error::Error for SettleError {}

/// The settlement sink — where a metered period becomes a conserving value flow.
///
/// This is the single seam the orchestrator drives, identical over every backend
/// (the [`crate::payable::PayableSettlement`] production rail, the node-API rail,
/// the verified pg store, and the [`TestConservingLedger`] test double). An
/// implementation MUST be:
/// - **conserving** — the payer is debited exactly what the beneficiary is
///   credited (per-asset Σδ = 0);
/// - **exactly-once** — settling the same `(lease_id, period)` twice moves value
///   only once (the second call returns the recorded receipt with `replayed`).
pub trait Settlement: Send + Sync {
    /// Settle one period's charge. Idempotent on `(lease_id, period)`.
    fn settle(&self, charge: &LeaseCharge) -> Result<SettleReceipt, SettleError>;

    /// The total amount settled for a lease across all its periods.
    fn settled_total(&self, lease_id: &str) -> i64;

    /// The **real funded balance** `holder` holds of `asset` on this rail — the
    /// authoritative admission read (the conserving ledger's reserve, or the live
    /// node's cell balance), NOT a self-asserted lease bool. An admission gate that
    /// must charge `holder` (e.g. a persistent server's per-period rent) reads THIS
    /// to confirm the reserve actually exists before provisioning real machines.
    ///
    /// Fail-closed default: `0` (unknown ⇒ refuse). An implementation that can read a
    /// real balance MUST override it; one that cannot read a balance authorizes no
    /// up-front-charged work, which is the safe floor.
    fn funded_balance(&self, _asset: &str, _holder: &str) -> i64 {
        0
    }

    /// The on-chain turn-receipt hash of the turn that settled `(lease_id,
    /// period)`, when this rail submitted a real turn and recorded its receipt.
    /// This is the value a sealed product receipt threads into its
    /// `turn_receipt_hash` view link (the receipt hex codec).
    ///
    /// Default: `None` (an in-process double, or a rail that has not confirmed
    /// the turn). A rail that records real turn hashes (the payable rail, the
    /// node-API rail with a durable ledger) overrides it.
    fn settled_turn_hash(&self, _lease_id: &str, _period: i64) -> Option<[u8; 32]> {
        None
    }
}

/// **The explicit test double**: a conserving in-process value ledger with the
/// same observable semantics as a real settlement rail, living entirely in one
/// process's memory.
///
/// Holdings are a per-`(asset, holder)` signed-`i64` map;
/// [`fund`](TestConservingLedger::fund) sets up a holder's balance (the
/// lessee's funded lease budget — the reserve); [`settle`](Settlement::settle)
/// moves value lessee → provider, conserving and exactly-once. The conserving
/// move runs through the substrate primitive
/// ([`crate::conserve::apply_conserving_transfer`]), so even the double
/// conserves by the proven `CellState` discipline.
///
/// It exists for offline tests and simulations. It is NOT a production
/// settlement path: nothing it records leaves the process, and it never yields
/// an on-chain turn ([`Settlement::settled_turn_hash`] is always `None`).
/// Production callers use [`crate::payable::PayableSettlement`] (or the
/// node-API / verified-store rails).
#[derive(Debug, Default)]
pub struct TestConservingLedger {
    /// `(asset, holder) -> balance`.
    balances: Mutex<HashMap<(String, String), i64>>,
    /// `(lease_id, period) -> the receipt settled for it` — the idempotency record.
    settled: Mutex<HashMap<(String, i64), SettleReceipt>>,
}

/// Compatibility alias for [`TestConservingLedger`], the explicit in-process
/// test double. Existing callers keep compiling; new code should name the
/// double for what it is (or use a real rail — see the module docs).
pub type ConservingLedger = TestConservingLedger;

impl TestConservingLedger {
    pub fn new() -> TestConservingLedger {
        TestConservingLedger::default()
    }

    /// Credit `holder` with `amount` of `asset` (e.g. fund the lessee's lease
    /// budget — the reserve the metered work is settled against). Returns the new
    /// balance.
    pub fn fund(&self, asset: &str, holder: &str, amount: i64) -> i64 {
        let mut g = self.balances.lock().expect("ledger poisoned");
        let e = g
            .entry((asset.to_string(), holder.to_string()))
            .or_insert(0);
        *e += amount;
        *e
    }

    /// Read `holder`'s balance of `asset` (`0` if it holds none).
    pub fn balance(&self, asset: &str, holder: &str) -> i64 {
        let g = self.balances.lock().expect("ledger poisoned");
        *g.get(&(asset.to_string(), holder.to_string()))
            .unwrap_or(&0)
    }

    /// The sum of every holder's balance of `asset` — the conservation witness.
    /// Funding aside, every settlement leaves this unchanged (Σδ = 0).
    pub fn total_supply(&self, asset: &str) -> i64 {
        let g = self.balances.lock().expect("ledger poisoned");
        g.iter()
            .filter(|((a, _), _)| a == asset)
            .map(|(_, v)| *v)
            .sum()
    }
}

impl Settlement for TestConservingLedger {
    fn settle(&self, charge: &LeaseCharge) -> Result<SettleReceipt, SettleError> {
        if charge.amount <= 0 {
            return Err(SettleError::NonPositiveAmount(charge.amount));
        }

        // Exactly-once + the value move are ONE atomic critical section. The dedup
        // lock is held across the check, the conserving transfer, AND the record
        // insert, so two concurrent settles of the same `(lease, period)` cannot both
        // pass the not-yet-settled check and both move value (a double-charge race).
        // Lock ordering is always `settled` → `balances`; no other path takes
        // `balances` before `settled`, so this cannot deadlock. (Regression: the
        // workload suite's §5.4 racing-settle scenario double-charged when the two
        // were separate critical sections.)
        let key = (charge.lease_id.clone(), charge.period);
        let mut settled = self.settled.lock().expect("ledger poisoned");
        if let Some(prior) = settled.get(&key) {
            if prior.amount != charge.amount || prior.asset != charge.asset {
                return Err(SettleError::Conflict {
                    lease_id: charge.lease_id.clone(),
                    period: charge.period,
                });
            }
            let mut replay = prior.clone();
            replay.replayed = true;
            return Ok(replay);
        }

        // The conserving move: debit payer, credit beneficiary together (Σδ = 0).
        // The move itself is performed by the conservation primitive
        // ([`crate::conserve::apply_conserving_transfer`]) — the kernel
        // `Effect::Transfer` paired-delta law, decided (in the `dregg-conserve`
        // lane) by the substrate's proven `CellState` signed-balance discipline
        // (`recTransfer_balanceSum_conserve`), NOT by hand-rolled arithmetic here.
        // The refuse-below-zero `InsufficientFunds` floor is the proven
        // `debit_balance` floor.
        let mut balances = self.balances.lock().expect("ledger poisoned");
        let payer_key = (charge.asset.clone(), charge.payer.clone());
        let benef_key = (charge.asset.clone(), charge.beneficiary.clone());
        let payer_balance = *balances.get(&payer_key).unwrap_or(&0);
        let beneficiary_balance = *balances.get(&benef_key).unwrap_or(&0);
        let moved = crate::conserve::apply_conserving_transfer(
            &charge.asset,
            &charge.payer,
            payer_balance,
            beneficiary_balance,
            charge.amount,
        )?;
        let new_payer = moved.new_payer;
        let new_benef = moved.new_beneficiary;
        balances.insert(payer_key, new_payer);
        balances.insert(benef_key, new_benef);
        drop(balances);

        let receipt = SettleReceipt {
            lease_id: charge.lease_id.clone(),
            period: charge.period,
            asset: charge.asset.clone(),
            amount: charge.amount,
            payer_balance: new_payer,
            beneficiary_balance: new_benef,
            replayed: false,
        };
        settled.insert(key, receipt.clone());
        Ok(receipt)
    }

    fn settled_total(&self, lease_id: &str) -> i64 {
        self.settled
            .lock()
            .expect("ledger poisoned")
            .iter()
            .filter(|((l, _), _)| l == lease_id)
            .map(|(_, r)| r.amount)
            .sum()
    }

    /// The real reserve `holder` holds — the materialized conserving balance, the
    /// authority an admission gate reads (not a self-asserted lease bool).
    fn funded_balance(&self, asset: &str, holder: &str) -> i64 {
        self.balance(asset, holder)
    }
}

/// Read a lease's committed meter charges from the Postgres outbox and settle each
/// through `sink` — the literal metering→Payable fold over the shared database.
///
/// This is the pg path the meter docs name: a durable run writes per-period charge
/// rows to [the settlement outbox](crate::METER_TABLE) (exactly-once via `ON CONFLICT DO
/// NOTHING`); this reads them back ([`read_meter_outbox`](crate::read_meter_outbox))
/// and settles each as a conserving transfer `payer → beneficiary`. Because both
/// the outbox row and the settlement are keyed `(lease_id, period)`, the fold is
/// exactly-once end to end: re-running it settles nothing new.
///
/// Returns the receipts in period order. The real deployment runs `sink` as a
/// dregg `Payable` so the settlement is itself an on-chain conserving `Transfer`.
#[cfg(feature = "pg")]
pub async fn settle_meter_outbox<S: Settlement>(
    pool: &sqlx::PgPool,
    sink: &S,
    lease_id: &str,
    payer: &str,
    beneficiary: &str,
    asset: &str,
) -> anyhow::Result<Vec<SettleReceipt>> {
    let rows = crate::read_meter_outbox(pool, lease_id).await?;
    let mut receipts = Vec::with_capacity(rows.len());
    for row in rows {
        let charge = LeaseCharge::new(payer, beneficiary, asset, lease_id, row.period, row.amount);
        let receipt = sink
            .settle(&charge)
            .map_err(|e| anyhow::anyhow!("settle period {}: {e}", row.period))?;
        receipts.push(receipt);
    }
    Ok(receipts)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn charge(lease: &str, period: i64, amount: i64) -> LeaseCharge {
        LeaseCharge::new("lessee", "provider", "USD", lease, period, amount)
    }

    #[test]
    fn settle_moves_value_and_conserves() {
        let l = TestConservingLedger::new();
        // Reserve: the lessee is funded with the lease budget.
        l.fund("USD", "lessee", 100);
        assert_eq!(l.total_supply("USD"), 100);

        let r = l.settle(&charge("lease-1", 1, 7)).expect("settle");
        assert!(!r.replayed);
        assert_eq!(r.payer_balance, 93);
        assert_eq!(r.beneficiary_balance, 7);
        // Value moved, none created or destroyed.
        assert_eq!(l.balance("USD", "lessee"), 93);
        assert_eq!(l.balance("USD", "provider"), 7);
        assert_eq!(l.total_supply("USD"), 100, "Σδ = 0 across the transfer");
    }

    #[test]
    fn settle_is_exactly_once_per_period() {
        let l = TestConservingLedger::new();
        l.fund("USD", "lessee", 100);

        let first = l.settle(&charge("lease-1", 1, 5)).unwrap();
        assert!(!first.replayed);
        // Re-settling the SAME period moves no value and reports the replay.
        let again = l.settle(&charge("lease-1", 1, 5)).unwrap();
        assert!(again.replayed);
        assert_eq!(again.amount, 5);

        // Only one charge landed.
        assert_eq!(l.balance("USD", "provider"), 5);
        assert_eq!(l.settled_total("lease-1"), 5);
    }

    #[test]
    fn distinct_periods_accumulate() {
        let l = TestConservingLedger::new();
        l.fund("USD", "lessee", 100);
        l.settle(&charge("lease-1", 1, 3)).unwrap();
        l.settle(&charge("lease-1", 2, 4)).unwrap();
        assert_eq!(l.settled_total("lease-1"), 7);
        assert_eq!(l.balance("USD", "provider"), 7);
        assert_eq!(l.balance("USD", "lessee"), 93);
    }

    #[test]
    fn over_funded_floor_refuses_to_overdraw() {
        let l = TestConservingLedger::new();
        l.fund("USD", "lessee", 2);
        // A charge beyond the reserve is refused — no settling unpaid work.
        assert!(matches!(
            l.settle(&charge("lease-1", 1, 5)),
            Err(SettleError::InsufficientFunds { .. })
        ));
        // Nothing moved.
        assert_eq!(l.total_supply("USD"), 2);
        assert_eq!(l.balance("USD", "provider"), 0);
    }

    #[test]
    fn same_key_different_terms_is_a_conflict() {
        let l = TestConservingLedger::new();
        l.fund("USD", "lessee", 100);
        l.settle(&charge("lease-1", 1, 5)).unwrap();
        assert!(matches!(
            l.settle(&charge("lease-1", 1, 9)),
            Err(SettleError::Conflict { .. })
        ));
    }

    #[test]
    fn non_positive_amount_refused() {
        let l = TestConservingLedger::new();
        l.fund("USD", "lessee", 100);
        assert!(matches!(
            l.settle(&charge("lease-1", 1, 0)),
            Err(SettleError::NonPositiveAmount(0))
        ));
    }
}
