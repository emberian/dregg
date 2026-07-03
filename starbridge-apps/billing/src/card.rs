//! # billing — the UI as a deos-view CARD (a `deos.ui.*` view-tree).
//!
//! The fourth axis of a modern starbridge-app: the app lives IN the deos world by shipping
//! its surface as a **renderer-independent card** — a serializable `deos.ui.*` element-tree.
//! The SAME tree renders three ways (native gpui in the cockpit, a browser HTML document, a
//! discord embed), all from this one piece of DATA. The app's contribution is the
//! view-tree JSON (pure `serde_json`, no renderer dependency); the deos world's renderers
//! consume it.
//!
//! ## The card shape — a live "estimate → charge under cap → seal the invoice" dashboard
//!
//! A titled column built from the rich deos-view vocabulary, surfacing the whole billing
//! story of an account:
//!
//!   * a **status header** — the app name + a row of static **cap-tier** `pill`s naming the
//!     two roles on the attenuation lattice (the ACCOUNT is charged + seals; the PROVIDER
//!     owns the account), and a `breadcrumb` of the billing lifecycle
//!     (Estimate → Charge → Invoice) with the current band marked;
//!   * a **"Spend cap" `section`** — the KILLER VISUAL is a `gauge` bound to
//!     [`SPENT_SLOT`](crate::SPENT_SLOT) over the demo cap (the budget consumed as charges
//!     accrue, refused at the ceiling — the 402), plus `bind`s on the per-period cap
//!     ([`CAP_SLOT`](crate::CAP_SLOT)) and the provider ([`PROVIDER_SLOT`](crate::PROVIDER_SLOT));
//!   * an **"Invoice" `section`** — the sealed-bill half: the committed invoice digest
//!     ([`INVOICE_DIGEST_SLOT`](crate::INVOICE_DIGEST_SLOT) — the invoice's own turn-receipt
//!     seal, an adept bone) and the billing-period start ([`START_SLOT`](crate::START_SLOT));
//!   * an **"Actions" `section`** of one `icon`+`button` row per service operation
//!     (`charge` / `seal` / `estimate` / `status`), each `button` carrying its `onClick`.
//!
//! The button `turn` names match the [`service`](crate::service) method vocabulary.

use serde_json::{Value, json};

use crate::service::{METHOD_CHARGE, METHOD_ESTIMATE, METHOD_SEAL, METHOD_STATUS};
use crate::{CAP_SLOT, INVOICE_DIGEST_SLOT, PROVIDER_SLOT, SPENT_SLOT, START_SLOT};

/// The demo per-period cap the spent gauge fills over — the budget the account is metered
/// against (the "spent / cap" denominator made visible).
pub const DEMO_CAP: u64 = 1_000;

/// A `deos.ui.text` node.
fn text(s: &str) -> Value {
    json!({ "kind": "text", "props": { "text": s } })
}

/// A static `deos.ui.pill` node — a colored status badge (no live slot).
fn pill(label: &str, tag: &str) -> Value {
    json!({ "kind": "pill", "props": { "text": label, "tag": tag } })
}

/// A `deos.ui.icon` node — a glyph indicator tinted by `tag`.
fn icon(glyph: &str, tag: &str) -> Value {
    json!({ "kind": "icon", "props": { "glyph": glyph, "tag": tag } })
}

/// A `deos.ui.divider` node — a full-width groove rule.
fn divider() -> Value {
    json!({ "kind": "divider", "props": {} })
}

/// A `deos.ui.row` node — a horizontal flex of children.
fn row(children: Vec<Value>) -> Value {
    json!({ "kind": "row", "props": {}, "children": children })
}

/// A `deos.ui.section` node — a titled, bordered container.
fn section(title: &str, tag: &str, children: Vec<Value>) -> Value {
    json!({ "kind": "section", "props": { "title": title, "tag": tag }, "children": children })
}

/// A `deos.ui.bind` node tagged with the model `slot` it re-reads + a label prefix and a
/// display `fmt` (`"id"` avatar-handle / `"hash"` short-hex / `"amount"` grouped / `"raw"`
/// plain). `adept` hides a dev-y row (a raw digest) from the simple projection.
fn bind(slot: usize, label: &str, fmt: &str, adept: bool) -> Value {
    json!({ "kind": "bind", "props": { "slot": slot, "label": label, "fmt": fmt, "adept": adept } })
}

/// A `deos.ui.gauge` node — a bound progress bar (`slot_value / max`, immediate-mode).
fn gauge(slot: usize, max: u64, label: &str) -> Value {
    json!({ "kind": "gauge", "props": { "slot": slot, "max": max, "label": label } })
}

/// A `deos.ui.breadcrumb` node — the lifecycle path; the `active` step is marked `›`.
fn breadcrumb(steps: &[&str], active: usize) -> Value {
    let items: Vec<Value> = steps
        .iter()
        .enumerate()
        .map(|(i, s)| {
            let label = if i == active {
                format!("› {s}")
            } else {
                s.to_string()
            };
            json!({ "label": label })
        })
        .collect();
    json!({ "kind": "breadcrumb", "props": { "items": items } })
}

/// A `deos.ui.button` node carrying its affordance payload `onClick = {turn, arg}`.
fn button(label: &str, turn: &str, arg: i64) -> Value {
    json!({
        "kind": "button",
        "props": { "label": label, "onClick": { "turn": turn, "arg": arg } }
    })
}

/// An action row — an `icon` + a service `button` (the verified-turn affordance).
fn action(glyph: &str, label: &str, turn: &str) -> Value {
    row(vec![icon(glyph, "accent"), button(label, turn, 0)])
}

/// **The billing card as a `deos.ui.*` view-tree** (a `serde_json::Value`).
///
/// A live billing dashboard telling the full "estimate → charge under cap → seal the
/// invoice" story: a status header (name + the two cap-tier pills + the lifecycle
/// breadcrumb), a "Spend cap" section whose KILLER VISUAL is the spent gauge (the budget
/// consumed, refused at the ceiling), an "Invoice" section surfacing the sealed invoice
/// digest + period start, and an "Actions" section of the charge / seal / estimate / status
/// buttons. Renderer-independent DATA. The button `turn` names are the
/// [`service`](crate::service) method symbols.
pub fn billing_card_value() -> Value {
    json!({
        "kind": "vstack",
        "props": {},
        "children": [
            row(vec![text("Billing Account"), pill("metered", "genuine")]),
            // The two roles on the attenuation lattice (cap tiers).
            row(vec![
                pill("account · charged", "accent"),
                pill("provider · owns", "muted"),
            ]),
            breadcrumb(&["Estimate", "Charge", "Invoice"], 1),
            divider(),
            section("Spend cap", "genuine", vec![
                // THE KILLER VISUAL: the budget consumed as charges accrue (402 at the ceiling).
                gauge(SPENT_SLOT as usize, DEMO_CAP, "spent "),
                bind(CAP_SLOT as usize, "cap · ", "amount", false),
                bind(PROVIDER_SLOT as usize, "provider · ", "id", false),
            ]),
            section("Invoice", "", vec![
                // The sealed invoice digest — the invoice's own turn-receipt seal (adept bone).
                bind(INVOICE_DIGEST_SLOT as usize, "sealed invoice · ", "hash", true),
                bind(START_SLOT as usize, "period start · ", "raw", false),
            ]),
            section("Actions", "", vec![
                action("$", "Charge",   METHOD_CHARGE),
                action("✓", "Seal",     METHOD_SEAL),
                action("≈", "Estimate", METHOD_ESTIMATE),
                action("≡", "Status",   METHOD_STATUS),
            ]),
        ]
    })
}

/// **The billing card as serialized `deos.ui.*` JSON** — the string a host serves / embeds
/// (`JSON.stringify(tree)` shape a `deos-view` renderer parses).
pub fn billing_card_json() -> String {
    serde_json::to_string(&billing_card_value()).expect("the billing card serializes")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn collect<'a>(node: &'a Value, kind: &str, out: &mut Vec<&'a Value>) {
        if node["kind"] == kind {
            out.push(node);
        }
        if let Some(children) = node["children"].as_array() {
            for c in children {
                collect(c, kind, out);
            }
        }
    }

    fn of_kind<'a>(card: &'a Value, kind: &str) -> Vec<&'a Value> {
        let mut out = Vec::new();
        collect(card, kind, &mut out);
        out
    }

    #[test]
    fn the_card_is_a_vstack_with_a_named_header() {
        let card = billing_card_value();
        assert_eq!(card["kind"], "vstack");
        let texts = of_kind(&card, "text");
        assert!(
            texts
                .iter()
                .any(|t| t["props"]["text"] == "Billing Account")
        );
    }

    #[test]
    fn the_two_cap_tiers_are_named_as_static_pills() {
        let card = billing_card_value();
        let pills: Vec<String> = of_kind(&card, "pill")
            .into_iter()
            .map(|p| p["props"]["text"].as_str().unwrap().to_string())
            .collect();
        assert!(pills.contains(&"account · charged".to_string()));
        assert!(pills.contains(&"provider · owns".to_string()));
    }

    #[test]
    fn the_lifecycle_breadcrumb_marks_the_charge_band() {
        let card = billing_card_value();
        let crumbs = of_kind(&card, "breadcrumb");
        assert_eq!(crumbs.len(), 1);
        let items = crumbs[0]["props"]["items"].as_array().unwrap();
        assert_eq!(items.len(), 3, "Estimate → Charge → Invoice");
        assert_eq!(items[1]["label"], "› Charge", "the active band is marked");
    }

    #[test]
    fn the_spend_gauge_reads_the_live_spent_slot() {
        let card = billing_card_value();
        let gauges = of_kind(&card, "gauge");
        assert_eq!(gauges.len(), 1, "the killer visual: the spent gauge");
        assert_eq!(gauges[0]["props"]["slot"], SPENT_SLOT as usize);
        assert_eq!(gauges[0]["props"]["max"], DEMO_CAP);
    }

    #[test]
    fn the_sections_surface_the_cap_then_the_invoice() {
        let card = billing_card_value();
        let titles: Vec<&str> = of_kind(&card, "section")
            .iter()
            .map(|s| s["props"]["title"].as_str().unwrap())
            .collect();
        assert_eq!(titles, vec!["Spend cap", "Invoice", "Actions"]);

        // The binds surface cap / provider (cap), then invoice digest / period start.
        let binds = of_kind(&card, "bind");
        let slots: Vec<u64> = binds
            .iter()
            .map(|b| b["props"]["slot"].as_u64().unwrap())
            .collect();
        assert_eq!(
            slots,
            vec![
                CAP_SLOT as u64,
                PROVIDER_SLOT as u64,
                INVOICE_DIGEST_SLOT as u64,
                START_SLOT as u64,
            ],
        );
    }

    #[test]
    fn the_sealed_invoice_digest_is_marked_adept() {
        let card = billing_card_value();
        let adept = of_kind(&card, "bind")
            .into_iter()
            .find(|b| b["props"]["slot"].as_u64() == Some(INVOICE_DIGEST_SLOT as u64))
            .and_then(|b| b["props"]["adept"].as_bool())
            .unwrap();
        assert!(adept, "the sealed invoice digest is a dev-y bone");
    }

    #[test]
    fn every_button_carries_its_service_method_as_the_turn_payload() {
        let card = billing_card_value();
        let buttons = of_kind(&card, "button");
        assert_eq!(buttons.len(), 4);
        let turns: Vec<&str> = buttons
            .iter()
            .map(|b| b["props"]["onClick"]["turn"].as_str().unwrap())
            .collect();
        assert_eq!(
            turns,
            vec![METHOD_CHARGE, METHOD_SEAL, METHOD_ESTIMATE, METHOD_STATUS]
        );
    }

    #[test]
    fn the_card_serializes_to_parseable_json() {
        let s = billing_card_json();
        let back: Value = serde_json::from_str(&s).expect("the card JSON parses");
        assert_eq!(back["kind"], "vstack");
        // header row, cap-tier row, breadcrumb, divider, Spend cap, Invoice, Actions.
        assert_eq!(back["children"].as_array().unwrap().len(), 7);
    }
}
