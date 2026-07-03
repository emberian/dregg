//! **Cost estimation**: estimate-before-you-charge. A PURE function over a
//! [`RateCard`](crate::RateCard): given a resource declaration (a resource + its expected
//! quantity over a period), compute the cost — so a caller sees the bill before committing
//! the spend.
//!
//! The estimate uses the SAME arithmetic a settled charge bills on
//! ([`RateCard::cost`](crate::RateCard::cost) = `quantity × unit_rate + flat`), so an
//! estimate of N units of a resource equals exactly what a charge of N units is billed —
//! the estimate matches the rate card, line by line and in total. This is a total
//! function with no cell, no turn, and no receipt (nothing has settled yet): it is the
//! `estimate` read seam the service face names as `Serviced` (never desugared to a turn).

use crate::usage::{BillableResource, RateCard};

/// A declared resource + its expected quantity over the estimate's period — the input a
/// caller supplies before spending.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResourceDeclaration {
    /// Which resource is being declared.
    pub resource: BillableResource,
    /// The expected quantity over the period, in the resource's natural unit.
    pub quantity: u64,
}

impl ResourceDeclaration {
    /// Declare `quantity` of `resource`.
    pub fn new(resource: BillableResource, quantity: u64) -> ResourceDeclaration {
        ResourceDeclaration { resource, quantity }
    }
}

/// One estimated line: the resource, the declared quantity, the rate applied, and the cost
/// it would incur. The estimate twin of an invoice [`LineItem`](crate::LineItem) — same
/// arithmetic, no receipts (nothing has settled yet).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EstimateLine {
    /// Which resource this line estimates.
    pub resource: BillableResource,
    /// The declared quantity.
    pub quantity: u64,
    /// The per-unit rate applied (from the card).
    pub unit_rate_units: i64,
    /// The flat per-op component (from the card).
    pub flat_units: i64,
    /// The estimated cost for this resource: `quantity × unit_rate + flat`.
    pub amount_units: i64,
}

/// A cost estimate over a set of declared resources.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Estimate {
    /// The period label the estimate is for (e.g. `"per month"`).
    pub period_label: String,
    /// The per-resource estimated lines.
    pub lines: Vec<EstimateLine>,
    /// The estimated total: `Σ` of every line.
    pub total_units: i64,
}

/// **Estimate the cost** of `declarations` over `period_label` against `card`. Each
/// declaration is costed `quantity × unit_rate + flat` — the exact charge arithmetic —
/// and the total is the sum. A pure total function.
pub fn estimate(
    declarations: &[ResourceDeclaration],
    card: &RateCard,
    period_label: impl Into<String>,
) -> Estimate {
    let lines: Vec<EstimateLine> = declarations
        .iter()
        .map(|d| EstimateLine {
            resource: d.resource,
            quantity: d.quantity,
            unit_rate_units: card.unit_rate_for(d.resource),
            flat_units: card.flat_for(d.resource),
            amount_units: card.cost(d.resource, d.quantity),
        })
        .collect();
    let total_units = lines.iter().map(|l| l.amount_units).sum();
    Estimate {
        period_label: period_label.into(),
        lines,
        total_units,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ── an estimate matches the rate card, line by line + total ──
    #[test]
    fn an_estimate_matches_the_rate_card() {
        let card = RateCard::default();
        let decls = vec![
            // 100 compute steps: 100 × 1 = 100.
            ResourceDeclaration::new(BillableResource::Compute, 100),
            // 50 MiB bandwidth: 50 × 5 = 250.
            ResourceDeclaration::new(BillableResource::Bandwidth, 50),
            // a 100-KiB site: op 10 + 100 × 1 = 110.
            ResourceDeclaration::new(BillableResource::Site, 100),
            // 30 uptime periods: 30 × 2 = 60.
            ResourceDeclaration::new(BillableResource::Service, 30),
        ];
        let est = estimate(&decls, &card, "per month");

        assert_eq!(est.lines.len(), 4);
        assert_eq!(est.lines[0].amount_units, 100);
        assert_eq!(est.lines[1].amount_units, 250);
        assert_eq!(est.lines[2].amount_units, 110);
        assert_eq!(
            est.lines[2].flat_units, 10,
            "the publish op is the site flat"
        );
        assert_eq!(est.lines[3].amount_units, 60);

        // The total is the sum, and each line equals `card.cost` exactly.
        assert_eq!(est.total_units, 100 + 250 + 110 + 60);
        for l in &est.lines {
            assert_eq!(l.amount_units, card.cost(l.resource, l.quantity));
        }
    }

    #[test]
    fn the_free_card_estimates_zero() {
        let est = estimate(
            &[ResourceDeclaration::new(BillableResource::Compute, 9_999)],
            &RateCard::free(),
            "free era",
        );
        assert_eq!(est.total_units, 0);
    }
}
