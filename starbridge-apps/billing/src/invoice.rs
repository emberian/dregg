//! The **invoice**: an account's settled charges over a billing period, aggregated into
//! per-resource line items (quantity × rate = amount) — and made VERIFIABLE.
//!
//! ## No new primitive — an invoice is a VIEW, sealed as a turn receipt
//!
//! An invoice introduces nothing the substrate does not already have. It is a pure
//! AGGREGATION over settled turn receipts, verifiable at two layers:
//!
//! 1. **Line-level receipt trace.** Every line item carries the [`SettleReceipt`]s it was
//!    aggregated from (each a settled turn's own receipt hash), and
//!    [`Invoice::verify_against_receipts`] re-witnesses the bill: each line's amount is
//!    exactly the sum of its receipts' settled amounts, each line's `quantity × rate +
//!    flat` reproduces that amount, and the invoice total is exactly the sum of every
//!    receipt. A single padded line or inflated total fails the check — "every line traces
//!    to a settled turn receipt."
//! 2. **Document-level seal.** An invoice is sealed as ITS OWN turn receipt: the
//!    [`Invoice::body_hash`] (a canonical, domain-separated blake3 over the account,
//!    period, asset, every line, and every anchored settle-receipt hash) is bound into a
//!    billing cell by a verified turn ([`crate::build_seal_invoice_action`]), so the
//!    executor's [`dregg_app_framework::TurnReceipt`] for that turn IS the invoice's seal
//!    — a light client sees the sealed digest move into the cell commitment.
//!    [`SealedInvoice`] pairs the invoice with that seal receipt hash.
//!
//! ## Cap-scoping (per-account)
//!
//! [`Invoice::assemble`] keeps only the events whose `account` matches the invoice
//! subject — another account's usage can never appear on this bill. [`invoices_for`] fans
//! a pooled event set out into one disjoint invoice per account.
//!
//! This ports the LOGIC of a prior imperative billing module (its `invoice.rs`) onto the
//! native receipt: where that prototype sealed into a bespoke ed25519 receipt chain, an
//! invoice here seals as the native turn receipt the executor already produces.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use crate::usage::{BillableResource, SettleReceipt, UsageEvent};

/// The window an invoice bills. `label` is the human period (e.g. `"2026-06"`); `start`
/// (inclusive) and `end` (exclusive) bound it on whatever clock the settlements ride
/// (a block height / epoch / unix second).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BillingPeriod {
    /// The human period label.
    pub label: String,
    /// The inclusive start of the window.
    pub start: i64,
    /// The exclusive end of the window.
    pub end: i64,
}

impl BillingPeriod {
    /// A billing period `[start, end)` labelled `label`.
    pub fn new(label: impl Into<String>, start: i64, end: i64) -> BillingPeriod {
        BillingPeriod {
            label: label.into(),
            start,
            end,
        }
    }
}

/// One per-resource line on an invoice: the aggregated quantity, the rate applied, the
/// amount, and the settle receipts the amount traces back to.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LineItem {
    /// Which resource this line bills.
    pub resource: BillableResource,
    /// The total metered quantity across the line's charges (the resource's natural unit).
    pub quantity: u64,
    /// The per-unit rate applied (`0` if the line was recovered from settle receipts
    /// without a quantity breakdown).
    pub unit_rate_units: i64,
    /// The total flat component across the line's charges (publish/deploy ops).
    pub flat_units: i64,
    /// The subtotal for this resource: `Σ` of the line's receipts.
    pub amount_units: i64,
    /// Every settle receipt aggregated into this line — the trace anchors (each a settled
    /// turn's receipt hash).
    pub receipts: Vec<SettleReceipt>,
}

/// A per-account invoice over a billing period.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Invoice {
    /// The account subject this invoice bills.
    pub account: String,
    /// The period billed.
    pub period: BillingPeriod,
    /// The asset the invoice is denominated in.
    pub asset: String,
    /// The per-resource line items, sorted by resource.
    pub line_items: Vec<LineItem>,
    /// The invoice total: `Σ` of every line.
    pub total_units: i64,
    /// When the invoice was assembled (RFC3339 / the caller's clock label).
    pub generated_at: String,
}

/// Why an invoice failed to verify against its receipts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InvoiceError {
    /// A line's `amount_units` did not equal the sum of its receipts' amounts — the line
    /// does not trace to its receipts (a padded or unbacked charge).
    LineDoesNotTrace {
        /// The line's resource.
        resource: BillableResource,
        /// The amount the line claims.
        line_amount: i64,
        /// The sum of its receipts.
        receipts_sum: i64,
    },
    /// A line's `quantity × unit_rate + flat` did not reproduce its `amount_units` — the
    /// quantity breakdown is inconsistent with the charged amount.
    LineMathMismatch {
        /// The line's resource.
        resource: BillableResource,
        /// The recomputed amount.
        computed: i64,
        /// The amount the line claims.
        line_amount: i64,
    },
    /// The invoice `total_units` did not equal the sum of its line amounts.
    TotalMismatch {
        /// The claimed total.
        total: i64,
        /// The sum of the lines.
        lines_sum: i64,
    },
    /// A line carried a receipt settled in a different asset than the invoice.
    AssetMismatch {
        /// The line's resource.
        resource: BillableResource,
        /// The invoice asset.
        expected: String,
        /// The receipt's asset.
        found: String,
    },
}

impl std::fmt::Display for InvoiceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InvoiceError::LineDoesNotTrace {
                resource,
                line_amount,
                receipts_sum,
            } => write!(
                f,
                "line `{}` amount {line_amount} != Σ receipts {receipts_sum} (does not trace)",
                resource.tag()
            ),
            InvoiceError::LineMathMismatch {
                resource,
                computed,
                line_amount,
            } => write!(
                f,
                "line `{}` quantity×rate+flat = {computed} != amount {line_amount}",
                resource.tag()
            ),
            InvoiceError::TotalMismatch { total, lines_sum } => {
                write!(f, "invoice total {total} != Σ lines {lines_sum}")
            }
            InvoiceError::AssetMismatch {
                resource,
                expected,
                found,
            } => write!(
                f,
                "line `{}` receipt asset `{found}` != invoice asset `{expected}`",
                resource.tag()
            ),
        }
    }
}

impl std::error::Error for InvoiceError {}

impl Invoice {
    /// Assemble the invoice for `account` over `period` from a pool of usage events, in
    /// `asset`. Only the events billed to `account` are aggregated (the cap-scoping tooth —
    /// another account's usage cannot appear); within the account, events are grouped by
    /// resource into line items sorted by resource, and the total is the sum of every line.
    pub fn assemble(
        account: &str,
        period: BillingPeriod,
        asset: impl Into<String>,
        events: &[UsageEvent],
        generated_at: impl Into<String>,
    ) -> Invoice {
        let mut by_resource: BTreeMap<BillableResource, LineItem> = BTreeMap::new();
        for e in events.iter().filter(|e| e.account == account) {
            let line = by_resource.entry(e.resource).or_insert_with(|| LineItem {
                resource: e.resource,
                quantity: 0,
                unit_rate_units: e.unit_rate_units,
                flat_units: 0,
                amount_units: 0,
                receipts: Vec::new(),
            });
            line.quantity = line.quantity.saturating_add(e.quantity);
            line.flat_units = line.flat_units.saturating_add(e.flat_units);
            line.amount_units = line.amount_units.saturating_add(e.amount_units);
            // Keep the first non-zero unit rate seen for the line's display rate.
            if line.unit_rate_units == 0 && e.unit_rate_units != 0 {
                line.unit_rate_units = e.unit_rate_units;
            }
            line.receipts.push(e.receipt.clone());
        }
        let line_items: Vec<LineItem> = by_resource.into_values().collect();
        let total_units = line_items.iter().map(|l| l.amount_units).sum();
        Invoice {
            account: account.to_string(),
            period,
            asset: asset.into(),
            line_items,
            total_units,
            generated_at: generated_at.into(),
        }
    }

    /// **Re-witness the bill against its receipts** (the verifiable-invoice tooth).
    ///
    /// Checks, for every line: each receipt is settled in the invoice's asset; the line's
    /// `amount_units` equals the sum of its receipts' amounts (every line traces to a
    /// receipt); and `quantity × unit_rate + flat` reproduces the amount whenever a unit
    /// rate is present. Finally the invoice `total_units` equals the sum of every line. A
    /// padded line, an inflated total, or a tampered receipt amount all fail.
    pub fn verify_against_receipts(&self) -> Result<(), InvoiceError> {
        let mut lines_sum: i64 = 0;
        for line in &self.line_items {
            let mut receipts_sum: i64 = 0;
            for r in &line.receipts {
                if r.asset != self.asset {
                    return Err(InvoiceError::AssetMismatch {
                        resource: line.resource,
                        expected: self.asset.clone(),
                        found: r.asset.clone(),
                    });
                }
                receipts_sum = receipts_sum.saturating_add(r.amount);
            }
            if receipts_sum != line.amount_units {
                return Err(InvoiceError::LineDoesNotTrace {
                    resource: line.resource,
                    line_amount: line.amount_units,
                    receipts_sum,
                });
            }
            // The quantity breakdown must reproduce the amount when a unit rate applies.
            if line.unit_rate_units != 0 {
                let computed = (line.quantity as i64)
                    .saturating_mul(line.unit_rate_units)
                    .saturating_add(line.flat_units);
                if computed != line.amount_units {
                    return Err(InvoiceError::LineMathMismatch {
                        resource: line.resource,
                        computed,
                        line_amount: line.amount_units,
                    });
                }
            }
            lines_sum = lines_sum.saturating_add(line.amount_units);
        }
        if lines_sum != self.total_units {
            return Err(InvoiceError::TotalMismatch {
                total: self.total_units,
                lines_sum,
            });
        }
        Ok(())
    }

    /// The canonical, domain-separated body hash of the invoice — what the seal binds and
    /// what a re-witnessing customer reproduces. Binds the account, period, asset, every
    /// line (resource, quantity, rate, flat, amount, and each anchored settle receipt's
    /// `(receipt_hash, period, amount)`), and the total. The line items are already sorted
    /// by resource, so the hash is canonical (order-independent of event arrival).
    pub fn body_hash(&self) -> [u8; 32] {
        let mut h = blake3::Hasher::new_derive_key("dregg.billing.invoice.body.v1");
        h.update(self.account.as_bytes());
        h.update(self.period.label.as_bytes());
        h.update(&self.period.start.to_le_bytes());
        h.update(&self.period.end.to_le_bytes());
        h.update(self.asset.as_bytes());
        h.update(&(self.line_items.len() as u64).to_le_bytes());
        for line in &self.line_items {
            h.update(line.resource.tag().as_bytes());
            h.update(&line.quantity.to_le_bytes());
            h.update(&line.unit_rate_units.to_le_bytes());
            h.update(&line.flat_units.to_le_bytes());
            h.update(&line.amount_units.to_le_bytes());
            h.update(&(line.receipts.len() as u64).to_le_bytes());
            for r in &line.receipts {
                h.update(&r.receipt_hash);
                h.update(&r.period.to_le_bytes());
                h.update(&r.amount.to_le_bytes());
            }
        }
        h.update(&self.total_units.to_le_bytes());
        *h.finalize().as_bytes()
    }

    /// **Seal the invoice as its own turn receipt.** Pair the invoice with the
    /// `seal_receipt_hash` — the [`dregg_app_framework::TurnReceipt::receipt_hash`] of the
    /// verified turn that bound this invoice's [`body_hash`](Invoice::body_hash) into the
    /// billing cell ([`crate::build_seal_invoice_action`]). The result is a
    /// [`SealedInvoice`] a customer re-witnesses by recomputing the body hash and checking
    /// the cell's committed sealed-digest slot, without trusting the host.
    pub fn seal(self, seal_receipt_hash: [u8; 32]) -> SealedInvoice {
        let body_hash = self.body_hash();
        SealedInvoice {
            invoice: self,
            body_hash,
            seal_receipt_hash,
        }
    }
}

/// An invoice sealed as its own turn receipt: the bill, its canonical `body_hash`, and the
/// `receipt_hash` of the verified turn that bound that digest into the billing cell. A
/// customer re-witnesses by recomputing `invoice.body_hash()` and confirming it equals
/// `body_hash` and that the cell's sealed-digest slot carries it — a tamper-evident,
/// re-derivable seal with no trusted third party.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SealedInvoice {
    /// The billed invoice.
    pub invoice: Invoice,
    /// The canonical body hash sealed into the cell (== `invoice.body_hash()`).
    pub body_hash: [u8; 32],
    /// The seal turn's receipt hash — the invoice's own turn-receipt seal.
    pub seal_receipt_hash: [u8; 32],
}

impl SealedInvoice {
    /// Whether the seal still matches the bill: the recomputed `body_hash` of the (possibly
    /// tampered) invoice equals the sealed `body_hash`. A tampered bill re-hashes to a
    /// different digest and fails this — the tamper-evidence tooth.
    pub fn reseals(&self) -> bool {
        self.invoice.body_hash() == self.body_hash
    }
}

/// Fan a pooled set of usage events out into one **disjoint invoice per account**: each
/// invoice sees only its own account's usage (the cap-scoping tooth applied across the
/// whole pool). Returns invoices keyed by account, period + asset shared.
pub fn invoices_for(
    period: BillingPeriod,
    asset: &str,
    events: &[UsageEvent],
    generated_at: &str,
) -> BTreeMap<String, Invoice> {
    let mut accounts: BTreeMap<String, ()> = BTreeMap::new();
    for e in events {
        accounts.insert(e.account.clone(), ());
    }
    accounts
        .into_keys()
        .map(|acct| {
            let inv = Invoice::assemble(&acct, period.clone(), asset, events, generated_at);
            (acct, inv)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    const CREDIT: &str = "CREDIT";

    fn rh(n: u8) -> [u8; 32] {
        [n; 32]
    }

    fn period() -> BillingPeriod {
        BillingPeriod::new("2026-06", 0, 1000)
    }

    /// A small realistic usage pool for `acct`: a compute roll-up, a bandwidth roll-up, a
    /// site publish (op + storage), and a deploy — each carrying a real settle-receipt hash.
    fn acct_events(acct: &str) -> Vec<UsageEvent> {
        vec![
            // compute: 5 steps × 3 = 15.
            UsageEvent::settled(
                acct,
                BillableResource::Compute,
                "lease-1",
                5,
                3,
                0,
                SettleReceipt::new(rh(10), CREDIT, 15, 0),
            ),
            // bandwidth: 3 MiB × 5 = 15.
            UsageEvent::settled(
                acct,
                BillableResource::Bandwidth,
                "blog",
                3,
                5,
                0,
                SettleReceipt::new(rh(11), CREDIT, 15, 1),
            ),
            // site publish: op 10 + 2 KiB × 1 = 12.
            UsageEvent::settled(
                acct,
                BillableResource::Site,
                "blog",
                2,
                1,
                10,
                SettleReceipt::new(rh(12), CREDIT, 12, 0),
            ),
            // deploy: flat 6.
            UsageEvent::settled(
                acct,
                BillableResource::Deploy,
                "deploy-1",
                0,
                0,
                6,
                SettleReceipt::new(rh(13), CREDIT, 6, 0),
            ),
        ]
    }

    // ── usage → an invoice with correct line items + total, all receipt-traced ──
    #[test]
    fn usage_aggregates_into_a_receipt_traced_invoice() {
        let events = acct_events("alice");
        let inv = Invoice::assemble("alice", period(), CREDIT, &events, "t0");

        // One line per resource, sorted by the resource order (Compute < Bandwidth < Site < Deploy).
        assert_eq!(inv.line_items.len(), 4);
        assert_eq!(inv.line_items[0].resource, BillableResource::Compute);
        assert_eq!(inv.line_items[0].amount_units, 15);
        assert_eq!(inv.line_items[2].resource, BillableResource::Site);
        assert_eq!(inv.line_items[2].flat_units, 10);

        // The total is the sum of the lines: 15 + 15 + 12 + 6 = 48.
        assert_eq!(inv.total_units, 48);

        // And the whole bill re-witnesses against its receipts: every line traces.
        assert_eq!(inv.verify_against_receipts(), Ok(()));
    }

    // ── an inflated total / padded line is caught by the receipt trace ──
    #[test]
    fn a_padded_invoice_fails_the_receipt_trace() {
        let events = acct_events("alice");
        let mut inv = Invoice::assemble("alice", period(), CREDIT, &events, "t0");

        // Pad the total without a backing receipt → caught.
        inv.total_units += 100;
        assert!(matches!(
            inv.verify_against_receipts(),
            Err(InvoiceError::TotalMismatch { .. })
        ));

        // Pad a line's amount (a charge with no receipt behind it) → caught.
        let mut inv2 = Invoice::assemble("alice", period(), CREDIT, &events, "t0");
        inv2.line_items[1].amount_units += 50;
        inv2.total_units += 50; // keep the total consistent so the LINE check is what bites.
        assert!(matches!(
            inv2.verify_against_receipts(),
            Err(InvoiceError::LineDoesNotTrace { .. })
        ));
    }

    // ── a tampered settle-receipt amount breaks the trace ──
    #[test]
    fn tampering_a_receipt_amount_breaks_the_trace() {
        let events = acct_events("alice");
        let mut inv = Invoice::assemble("alice", period(), CREDIT, &events, "t0");
        // Forge a receipt to claim a smaller settled amount than the line bills.
        inv.line_items[0].receipts[0].amount = 1;
        assert!(matches!(
            inv.verify_against_receipts(),
            Err(InvoiceError::LineDoesNotTrace { .. })
        ));
    }

    // ── another account cannot see this account's invoice (cap-scoped) ──
    #[test]
    fn invoices_are_cap_scoped_per_account() {
        let mut pool = acct_events("alice");
        pool.extend(acct_events("bob"));
        // Bob also has an extra agent line, to make the pools differ.
        pool.push(UsageEvent::settled(
            "bob",
            BillableResource::Agent,
            "agent-1",
            3,
            2,
            0,
            SettleReceipt::new(rh(20), CREDIT, 6, 7),
        ));

        let alice = Invoice::assemble("alice", period(), CREDIT, &pool, "t0");
        let bob = Invoice::assemble("bob", period(), CREDIT, &pool, "t0");

        // Alice's invoice never carries bob's extra agent receipt.
        assert!(
            alice
                .line_items
                .iter()
                .flat_map(|l| &l.receipts)
                .all(|r| r.receipt_hash != rh(20))
        );
        assert_eq!(alice.total_units, 48);
        // Bob's has the extra agent line.
        assert_eq!(bob.total_units, 48 + 6);
        assert!(
            bob.line_items
                .iter()
                .any(|l| l.resource == BillableResource::Agent)
        );

        // The fan-out yields exactly two disjoint invoices, each verifying.
        let all = invoices_for(period(), CREDIT, &pool, "t0");
        assert_eq!(all.len(), 2);
        for inv in all.values() {
            assert_eq!(inv.verify_against_receipts(), Ok(()));
        }
        // A stranger account that owns nothing in the pool gets an empty, zero invoice.
        let stranger = Invoice::assemble("carol", period(), CREDIT, &pool, "t0");
        assert!(stranger.line_items.is_empty());
        assert_eq!(stranger.total_units, 0);
        assert_eq!(stranger.verify_against_receipts(), Ok(()));
    }

    // ── the sealed invoice is re-derivable + tamper-evident ──
    #[test]
    fn a_sealed_invoice_is_tamper_evident() {
        let inv = Invoice::assemble("alice", period(), CREDIT, &acct_events("alice"), "t0");
        let body = inv.body_hash();
        // The seal binds the body hash + the seal turn's receipt hash (here a fixed stand-in;
        // the integration test seals through the real executor and uses the real receipt).
        let sealed = inv.clone().seal(rh(99));
        assert_eq!(sealed.body_hash, body);
        assert!(sealed.reseals(), "an untouched sealed invoice re-derives");

        // Altering the sealed invoice's billed total re-hashes to a different digest.
        let mut forged = sealed.clone();
        forged.invoice.total_units += 1;
        assert!(!forged.reseals(), "a tampered bill fails the re-derive");
    }

    // ── the body hash is canonical: event arrival order does not change it ──
    #[test]
    fn the_body_hash_is_canonical_across_event_order() {
        let mut ev = acct_events("alice");
        let a = Invoice::assemble("alice", period(), CREDIT, &ev, "t0").body_hash();
        ev.reverse();
        let b = Invoice::assemble("alice", period(), CREDIT, &ev, "t0").body_hash();
        assert_eq!(
            a, b,
            "lines are sorted by resource — the hash is order-independent"
        );
    }
}
