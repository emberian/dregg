//! The billing **source layer**: the per-resource rate card, the billable-resource
//! taxonomy, and the normalized [`UsageEvent`] — one *settled* charge attributed to
//! an account, carrying the **settle-receipt hash** it traces back to.
//!
//! ## Where the usage comes from (settled turns, not a new counter)
//!
//! This crate does not meter. Every [`UsageEvent`] is a VIEW of a charge that some
//! upstream turn already SETTLED: a value move committed by the executor, whose
//! [`dregg_app_framework::TurnReceipt`] is the tamper-evident proof it happened. The
//! anchor a line item carries is that receipt's canonical hash
//! ([`dregg_app_framework::TurnReceipt::receipt_hash`], a domain-separated blake3 over
//! the turn/effects/pre/post state) — a 32-byte [`SettleReceipt::receipt_hash`]. "Every
//! invoice line traces to a settled turn receipt" is the verifiable-bill tooth: the bill
//! is a re-derivable AGGREGATION over receipts a non-witness (the customer) already
//! holds, never a mystery charge.
//!
//! This mirrors the LOGIC of a prior imperative billing module (its `usage.rs`), but
//! re-homed onto the native receipt: where that prototype anchored a line to a
//! `(lease_id, period)` string key from a bespoke settle ledger, a line here anchors to
//! the native [`SettleReceipt`] — the settled turn's own receipt hash + the amount it
//! moved. No new primitive: the settle receipt is the turn receipt the executor already
//! produced.

use serde::{Deserialize, Serialize};

/// A billable resource — the line-item taxonomy an invoice groups usage by. The
/// declaration order is the canonical line-item sort order (an invoice's lines are
/// sorted by it, so a bill's `body_hash` is canonical regardless of event arrival
/// order).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum BillableResource {
    /// A durable-execution lease's metered compute (the primary agent-economy resource —
    /// see the sibling `starbridge-apps/execution-lease` crate the charges settle from).
    Compute,
    /// An agent run's metered calls/steps.
    Agent,
    /// Bytes served out, billed per MiB.
    Bandwidth,
    /// Object-storage bytes held, billed per GiB-period.
    Storage,
    /// A published static site: the publish op + per-KiB stored bytes.
    Site,
    /// A persistent service's per-wall-clock-period uptime.
    Service,
    /// A deploy operation (flat).
    Deploy,
}

impl BillableResource {
    /// The canonical billing tag (the line-item label + the invoice field key).
    pub fn tag(self) -> &'static str {
        match self {
            BillableResource::Compute => "compute",
            BillableResource::Agent => "agent",
            BillableResource::Bandwidth => "bandwidth",
            BillableResource::Storage => "storage",
            BillableResource::Site => "site",
            BillableResource::Service => "service",
            BillableResource::Deploy => "deploy",
        }
    }

    /// Decode a resource from a tag. An unknown tag is `None`.
    pub fn from_tag(tag: &str) -> Option<BillableResource> {
        Some(match tag {
            "compute" => BillableResource::Compute,
            "agent" => BillableResource::Agent,
            "bandwidth" => BillableResource::Bandwidth,
            "storage" => BillableResource::Storage,
            "site" => BillableResource::Site,
            "service" | "uptime" => BillableResource::Service,
            "deploy" => BillableResource::Deploy,
            _ => return None,
        })
    }
}

/// The per-resource price list, in the value asset's smallest unit. The single rate card
/// [estimation](crate::estimate) costs against and an invoice line item's
/// `unit_rate_units` is read from. `quantity × unit_rate + flat` is the one arithmetic an
/// estimate and a bill both use — so an estimate of N units of a resource equals exactly
/// what a settled charge of N units bills.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct RateCard {
    /// Cost per durable-compute step.
    pub compute_units_per_step: i64,
    /// Cost per agent call/step.
    pub agent_units_per_call: i64,
    /// Cost per MiB (rounded up) of bytes served.
    pub bandwidth_units_per_mib: i64,
    /// Cost per GiB-period of object storage held.
    pub storage_units_per_gib: i64,
    /// Cost per KiB (rounded up) of stored site bytes.
    pub site_units_per_kib: i64,
    /// Flat cost per publish op (the [`Site`](BillableResource::Site) flat).
    pub publish_op_units: i64,
    /// Cost per service uptime period.
    pub service_units_per_period: i64,
    /// Flat cost per deploy op (the [`Deploy`](BillableResource::Deploy) flat).
    pub deploy_op_units: i64,
}

impl Default for RateCard {
    /// A sensible default price list.
    fn default() -> RateCard {
        RateCard {
            compute_units_per_step: 1,
            agent_units_per_call: 1,
            bandwidth_units_per_mib: 5,
            storage_units_per_gib: 3,
            site_units_per_kib: 1,
            publish_op_units: 10,
            service_units_per_period: 2,
            deploy_op_units: 6,
        }
    }
}

impl RateCard {
    /// A free price list (every resource costs zero) — the subsidized early era.
    pub fn free() -> RateCard {
        RateCard {
            compute_units_per_step: 0,
            agent_units_per_call: 0,
            bandwidth_units_per_mib: 0,
            storage_units_per_gib: 0,
            site_units_per_kib: 0,
            publish_op_units: 0,
            service_units_per_period: 0,
            deploy_op_units: 0,
        }
    }

    /// The per-unit (per-quantity) rate for `resource`. For a [`Site`](BillableResource::Site)
    /// this is the per-KiB storage rate (the op cost is the [`flat_for`](RateCard::flat_for)).
    pub fn unit_rate_for(&self, resource: BillableResource) -> i64 {
        match resource {
            BillableResource::Compute => self.compute_units_per_step,
            BillableResource::Agent => self.agent_units_per_call,
            BillableResource::Bandwidth => self.bandwidth_units_per_mib,
            BillableResource::Storage => self.storage_units_per_gib,
            BillableResource::Site => self.site_units_per_kib,
            BillableResource::Service => self.service_units_per_period,
            BillableResource::Deploy => 0,
        }
    }

    /// The flat (per-op, quantity-independent) cost for `resource`: the publish op for a
    /// [`Site`](BillableResource::Site), the deploy op for a [`Deploy`](BillableResource::Deploy),
    /// else `0`.
    pub fn flat_for(&self, resource: BillableResource) -> i64 {
        match resource {
            BillableResource::Site => self.publish_op_units,
            BillableResource::Deploy => self.deploy_op_units,
            _ => 0,
        }
    }

    /// The cost of `quantity` of `resource` at this rate card: `quantity × unit_rate +
    /// flat`. The exact arithmetic estimation and a line item both use.
    pub fn cost(&self, resource: BillableResource, quantity: u64) -> i64 {
        (quantity as i64)
            .saturating_mul(self.unit_rate_for(resource))
            .saturating_add(self.flat_for(resource))
    }
}

/// The settled charge a [`UsageEvent`] traces back to — the receipt anchor that makes
/// the invoice verifiable. It is the native turn receipt of the settling value move:
///
///  * [`receipt_hash`](SettleReceipt::receipt_hash) — the settling turn's canonical
///    receipt hash ([`dregg_app_framework::TurnReceipt::receipt_hash`]). The exactly-once
///    identity of the settlement (a re-witnessing customer re-derives it from the receipt
///    they hold), and the per-line trace anchor bound into the invoice `body_hash`.
///  * [`amount`](SettleReceipt::amount) — the value moved payer → provider by that turn.
///  * [`asset`](SettleReceipt::asset) — the asset it was denominated in.
///  * [`period`](SettleReceipt::period) — the period ordinal within the settlement stream
///    (the settle window the charge landed in).
///
/// "Every invoice line traces to one of these" is the verifiable-bill tooth.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SettleReceipt {
    /// The settling turn's canonical receipt hash — the settle-receipt anchor.
    pub receipt_hash: [u8; 32],
    /// The asset the charge was denominated in.
    pub asset: String,
    /// The value moved payer → provider for this charge.
    pub amount: i64,
    /// The period ordinal within the settlement stream.
    pub period: i64,
}

impl SettleReceipt {
    /// A settle-receipt anchor over the settling turn's `receipt_hash`.
    pub fn new(
        receipt_hash: [u8; 32],
        asset: impl Into<String>,
        amount: i64,
        period: i64,
    ) -> SettleReceipt {
        SettleReceipt {
            receipt_hash,
            asset: asset.into(),
            amount,
            period,
        }
    }
}

/// One normalized usage event: a settled charge attributed to an account, carrying the
/// [`SettleReceipt`] it traces back to and the `quantity × rate` breakdown.
///
/// `amount_units == quantity × unit_rate_units + flat_units` and (for a well-formed event
/// sourced from a real settled charge) `amount_units == receipt.amount`. A charge
/// recovered from a settle receipt alone ([`from_settle`](UsageEvent::from_settle))
/// carries the amount without the quantity breakdown (the settling turn moved a value, not
/// a quantity), so it sets `quantity = 0`, `unit_rate = 0`, `flat = amount` — the line
/// still traces to the receipt and totals exactly, it just lacks the unit breakdown.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct UsageEvent {
    /// The account the charge is billed to (the payer / owner).
    pub account: String,
    /// Which resource was billed.
    pub resource: BillableResource,
    /// The specific resource billed (a lease id / site / service / deploy id).
    pub subject: String,
    /// The metered quantity, in the resource's natural unit (steps / MiB / periods / …).
    pub quantity: u64,
    /// The per-unit rate applied.
    pub unit_rate_units: i64,
    /// A flat per-op cost (e.g. the publish op cost); `0` for most resources.
    pub flat_units: i64,
    /// The value charged: `quantity × unit_rate + flat`.
    pub amount_units: i64,
    /// The settle receipt this event traces back to.
    pub receipt: SettleReceipt,
}

impl UsageEvent {
    /// A settled usage event with the full `quantity × rate` breakdown. `amount_units` is
    /// computed `quantity × unit_rate + flat`; a well-formed `receipt.amount` equals it
    /// (asserted by [`is_consistent`](UsageEvent::is_consistent) and the invoice
    /// receipt-trace check).
    pub fn settled(
        account: impl Into<String>,
        resource: BillableResource,
        subject: impl Into<String>,
        quantity: u64,
        unit_rate_units: i64,
        flat_units: i64,
        receipt: SettleReceipt,
    ) -> UsageEvent {
        let amount_units = (quantity as i64)
            .saturating_mul(unit_rate_units)
            .saturating_add(flat_units);
        UsageEvent {
            account: account.into(),
            resource,
            subject: subject.into(),
            quantity,
            unit_rate_units,
            flat_units,
            amount_units,
            receipt,
        }
    }

    /// A usage event recovered from a settle receipt alone (the amount was settled, but no
    /// quantity breakdown is recorded on the settling turn): the whole amount is carried as
    /// a flat, and the caller supplies the `resource`/`subject` the charge was for.
    pub fn from_settle(
        account: impl Into<String>,
        resource: BillableResource,
        subject: impl Into<String>,
        receipt: SettleReceipt,
    ) -> UsageEvent {
        let amount_units = receipt.amount;
        UsageEvent {
            account: account.into(),
            resource,
            subject: subject.into(),
            quantity: 0,
            unit_rate_units: 0,
            flat_units: amount_units,
            amount_units,
            receipt,
        }
    }

    /// Whether the event's breakdown is internally consistent: the computed `quantity ×
    /// unit_rate + flat` equals both `amount_units` and the anchored `receipt.amount`. A
    /// forged event (an amount that does not match its receipt or its own breakdown) fails
    /// this and the invoice receipt-trace check.
    pub fn is_consistent(&self) -> bool {
        let computed = (self.quantity as i64)
            .saturating_mul(self.unit_rate_units)
            .saturating_add(self.flat_units);
        computed == self.amount_units && self.amount_units == self.receipt.amount
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rh(n: u8) -> [u8; 32] {
        [n; 32]
    }

    #[test]
    fn resource_tag_roundtrips() {
        for r in [
            BillableResource::Compute,
            BillableResource::Agent,
            BillableResource::Bandwidth,
            BillableResource::Storage,
            BillableResource::Site,
            BillableResource::Service,
            BillableResource::Deploy,
        ] {
            assert_eq!(BillableResource::from_tag(r.tag()), Some(r));
        }
        assert_eq!(
            BillableResource::from_tag("uptime"),
            Some(BillableResource::Service)
        );
        assert_eq!(BillableResource::from_tag("nonsense"), None);
    }

    #[test]
    fn rate_card_cost_is_quantity_times_rate_plus_flat() {
        let card = RateCard::default();
        // a site of 4 KiB: op 10 + 4 × 1 = 14.
        assert_eq!(card.cost(BillableResource::Site, 4), 14);
        // bandwidth of 3 MiB: 3 × 5 = 15.
        assert_eq!(card.cost(BillableResource::Bandwidth, 3), 15);
        // a deploy: flat 6, quantity-independent.
        assert_eq!(card.cost(BillableResource::Deploy, 0), 6);
        // free card: everything 0.
        assert_eq!(RateCard::free().cost(BillableResource::Compute, 9_999), 0);
    }

    #[test]
    fn a_settled_event_is_consistent_with_its_receipt() {
        let r = SettleReceipt::new(rh(1), "CREDIT", 15, 1);
        let e = UsageEvent::settled("acct", BillableResource::Bandwidth, "blog", 3, 5, 0, r);
        assert_eq!(e.amount_units, 15);
        assert!(e.is_consistent());
    }

    #[test]
    fn a_tampered_receipt_amount_breaks_consistency() {
        // The receipt says 99 but the breakdown computes 15 — a forged line.
        let r = SettleReceipt::new(rh(2), "CREDIT", 99, 1);
        let e = UsageEvent::settled("acct", BillableResource::Bandwidth, "blog", 3, 5, 0, r);
        assert!(!e.is_consistent());
    }

    #[test]
    fn settle_recovery_carries_the_amount_as_a_flat() {
        let r = SettleReceipt::new(rh(3), "CREDIT", 4, 0);
        let e = UsageEvent::from_settle("acct", BillableResource::Compute, "lease-7", r);
        assert_eq!(e.resource, BillableResource::Compute);
        assert_eq!(e.amount_units, 4);
        assert!(e.is_consistent(), "flat == amount == receipt.amount");
    }
}
