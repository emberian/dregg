//! # edge-mandate — the UI as a deos-view CARD (a `deos.ui.*` view-tree).
//!
//! The fourth axis of a modern starbridge-app: the app lives IN the deos world by
//! shipping its surface as a **renderer-independent card** — a serializable
//! `deos.ui.*` element-tree. The SAME tree renders three ways (native gpui pixels
//! in the cockpit, a browser-loadable HTML document, and a discord embed) from this
//! one piece of DATA.
//!
//! ## Why the card is DATA, not a renderer call
//!
//! `deos-view` pulls both the SpiderMonkey and the gpui native elephants, so it is a
//! STANDALONE workspace EXCLUDED from the repo-root workspace. A starbridge-app must
//! never depend on it — that would feature-unify the elephants onto the main build.
//! So the app's contribution is the **view-tree JSON** (this module): pure
//! `serde_json`, no elephant. The deos world's renderers consume it.
//!
//! ## The card shape — a live edge-mandate dashboard
//!
//! A titled column built from the rich deos-view vocabulary:
//!
//!   - a **status header** — the app name + a LIVE `pill` reading [`REVOKED_SLOT`]
//!     (`ACTIVE`; a revoked mandate reads `REVOKED`);
//!   - a **role row** of static `pill`s naming the two parties on the attenuation
//!     lattice (the OPERATOR grants; the SUBJECT spends within the grant);
//!   - a **lifecycle `breadcrumb`** (grant → enrol → spend → revoke) with the
//!     current step marked;
//!   - an **"Authority" `section`** surfacing the LIVE mandate: the KILLER VISUAL —
//!     a `gauge` on the spend meter ([`SPENT_SLOT`]) filling toward the sealed
//!     budget ceiling (the conserved `spent ≤ budget` the executor's `AffineLe` gate
//!     enforces), plus `bind`s on the [`BUDGET_SLOT`], the [`SPENT_SLOT`], the
//!     [`ACCOUNT_SLOT`] account, and (adept-only) the sealed [`SUBJECT_SLOT`] /
//!     [`CAPS_DIGEST_SLOT`] digests + the no-replay [`EPOCH_SLOT`];
//!   - an **"Actions" `section`** of one `button` per mutating method
//!     (`enrol` / `spend` / `revoke`), each carrying its `onClick = { turn, arg }` —
//!     the EXACT cap-gated verified turn a click fires through the
//!     [`invoke()`](crate::service) seam.
//!
//! The button `turn` names match the [`service`](crate::service) method vocabulary
//! so the card and the service cell speak the same mandate.

use serde_json::{Value, json};

use crate::service::{METHOD_ENROL, METHOD_REVOKE, METHOD_SPEND};
use crate::{
    ACCOUNT_SLOT, BUDGET_SLOT, CAPS_DIGEST_SLOT, EPOCH_SLOT, REVOKED_SLOT, SPENT_SLOT, SUBJECT_SLOT,
};

/// The spend-gauge denominator — a representative budget ceiling ($50.00 in cents)
/// so a fully-spent mandate fills the gauge.
const BUDGET_GAUGE_MAX: u64 = 5_000;

/// A `deos.ui.text` node.
fn text(s: &str) -> Value {
    json!({ "kind": "text", "props": { "text": s } })
}

/// A static `deos.ui.pill` node — a colored status badge (no live slot).
fn pill(label: &str, tag: &str) -> Value {
    json!({ "kind": "pill", "props": { "text": label, "tag": tag } })
}

/// A LIVE `deos.ui.pill` node — reads `slot` immediate-mode and maps the value to a
/// word + color via `cases`. `text`/`tag` are the static fallback.
fn pill_live(slot: u8, label: &str, tag: &str, cases: Value) -> Value {
    json!({ "kind": "pill", "props": { "text": label, "tag": tag, "slot": slot as usize, "cases": cases } })
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

/// A `deos.ui.bind` node tagged with the model `slot` it re-reads + a label prefix
/// and a display `fmt` (`"id"` / `"hash"` / `"amount"` / `"raw"`).
fn bind(slot: u8, label: &str, fmt: &str) -> Value {
    json!({ "kind": "bind", "props": { "slot": slot as usize, "label": label, "fmt": fmt } })
}

/// A `deos.ui.bind` node marked `adept` — hidden in the simple projection; revealed
/// in the adept "see the bones" view.
fn bind_adept(slot: u8, label: &str, fmt: &str) -> Value {
    json!({ "kind": "bind", "props": { "slot": slot as usize, "label": label, "fmt": fmt, "adept": true } })
}

/// A `deos.ui.gauge` node — a bound progress bar (`slot_value / max`, immediate-mode).
fn gauge(slot: u8, max: u64, label: &str, adept: bool) -> Value {
    json!({ "kind": "gauge", "props": { "slot": slot as usize, "max": max, "label": label, "adept": adept } })
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

/// An action row — an `icon` + a method `button` (the verified-turn affordance).
fn action(glyph: &str, label: &str, turn: &str) -> Value {
    row(vec![icon(glyph, "accent"), button(label, turn, 0)])
}

/// **The edge-mandate card as a `deos.ui.*` view-tree** (a `serde_json::Value`).
///
/// A live mandate surface: a status header (name + a live `ACTIVE`/`REVOKED` pill),
/// a role row, a lifecycle breadcrumb, an "Authority" section surfacing the KILLER
/// VISUAL — the spend gauge filling toward the sealed budget (`spent / budget`) —
/// plus the budget / spend / account binds and the adept-only sealed digests, and an
/// "Actions" section of the three icon-labelled mutating-method buttons.
/// Renderer-independent DATA. The button `turn` names are the
/// [`service`](crate::service) method symbols.
pub fn mandate_card_value() -> Value {
    json!({
        "kind": "vstack",
        "props": {},
        "children": [
            // The header status pill is LIVE: it reads REVOKED and shows whether the
            // mandate is live. revoked=1 => REVOKED; else falls through to ACTIVE.
            row(vec![text("Edge Mandate"), pill_live(REVOKED_SLOT, "ACTIVE", "genuine", json!([
                { "value": 1, "label": "REVOKED", "tag": "danger" },
            ]))]),
            // The two roles on the attenuation lattice: the operator grants (and can
            // revoke); the subject spends within the granted budget + tool-set.
            row(vec![
                pill("operator · grants", "accent"),
                pill("subject · spends", "muted"),
            ]),
            breadcrumb(&["Grant", "Enrol", "Spend", "Revoke"], 1),
            divider(),
            section("Authority", "genuine", vec![
                gauge(SPENT_SLOT, BUDGET_GAUGE_MAX, "spend → budget ", false),
                // The conserved bound the executor's AffineLe gate enforces.
                text("spent ≤ budget (the AffineLe sub-budget tooth)"),
                bind(BUDGET_SLOT, "budget · ", "amount"),
                bind(SPENT_SLOT, "spent · ", "amount"),
                bind(ACCOUNT_SLOT, "account · ", "id"),
                // The sealed identity / caps digests + the no-replay epoch — internal
                // bookkeeping, adept-only.
                bind_adept(SUBJECT_SLOT, "subject key · ", "hash"),
                bind_adept(CAPS_DIGEST_SLOT, "caps digest · ", "hash"),
                bind_adept(EPOCH_SLOT, "epoch · ", "raw"),
            ]),
            section("Actions", "", vec![
                action("＋", "Enrol",  METHOD_ENROL),
                action("→", "Spend",  METHOD_SPEND),
                action("⊘", "Revoke", METHOD_REVOKE),
            ]),
        ]
    })
}

/// **The edge-mandate card as serialized `deos.ui.*` JSON** — byte-for-byte the
/// `JSON.stringify(tree)` shape a `deos-view` renderer parses. This is the string a
/// host serves / embeds.
pub fn mandate_card_json() -> String {
    serde_json::to_string(&mandate_card_value()).expect("the mandate card serializes")
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
    fn the_card_is_a_vstack_with_a_named_header_and_a_live_status_pill() {
        let card = mandate_card_value();
        assert_eq!(card["kind"], "vstack");
        let texts = of_kind(&card, "text");
        assert!(
            texts.iter().any(|t| t["props"]["text"] == "Edge Mandate"),
            "the header names the app"
        );
        // The header pill is LIVE: it reads REVOKED_SLOT and maps the value to a word.
        let live = of_kind(&card, "pill")
            .into_iter()
            .find(|p| p["props"].get("slot").is_some())
            .expect("exactly one live status pill");
        assert_eq!(live["props"]["text"], "ACTIVE", "the static fallback word");
        assert_eq!(live["props"]["slot"], REVOKED_SLOT as usize);
        let cases = live["props"]["cases"].as_array().unwrap();
        assert_eq!(cases.len(), 1, "revoked=1 => REVOKED");
        assert_eq!(cases[0]["value"], 1);
        assert_eq!(cases[0]["label"], "REVOKED");
    }

    #[test]
    fn the_role_row_names_the_operator_and_subject() {
        let card = mandate_card_value();
        let static_pills: Vec<String> = of_kind(&card, "pill")
            .into_iter()
            .filter(|p| p["props"].get("slot").is_none())
            .map(|p| p["props"]["text"].as_str().unwrap().to_string())
            .collect();
        assert_eq!(static_pills, vec!["operator · grants", "subject · spends"]);
    }

    #[test]
    fn the_authority_section_names_the_conserved_affine_bound() {
        let card = mandate_card_value();
        let texts = of_kind(&card, "text");
        assert!(
            texts
                .iter()
                .any(|t| t["props"]["text"].as_str().unwrap().contains("AffineLe")),
            "the conserved spent ≤ budget bound is named"
        );
    }

    #[test]
    fn the_spend_gauge_reads_the_live_meter_filling_toward_budget() {
        let card = mandate_card_value();
        let gauges = of_kind(&card, "gauge");
        assert_eq!(gauges.len(), 1, "one spend gauge");
        assert_eq!(gauges[0]["props"]["slot"], SPENT_SLOT as usize);
        assert_eq!(gauges[0]["props"]["max"], BUDGET_GAUGE_MAX);
    }

    #[test]
    fn the_binds_surface_budget_spend_account_and_the_adept_digests() {
        let card = mandate_card_value();
        let binds = of_kind(&card, "bind");
        let slots: Vec<u64> = binds
            .iter()
            .map(|b| b["props"]["slot"].as_u64().unwrap())
            .collect();
        assert_eq!(
            slots,
            vec![
                BUDGET_SLOT as u64,
                SPENT_SLOT as u64,
                ACCOUNT_SLOT as u64,
                SUBJECT_SLOT as u64,
                CAPS_DIGEST_SLOT as u64,
                EPOCH_SLOT as u64,
            ]
        );
        // The sealed identity / caps digests + epoch are adept-only.
        for slot in [SUBJECT_SLOT, CAPS_DIGEST_SLOT, EPOCH_SLOT] {
            let b = binds
                .iter()
                .find(|b| b["props"]["slot"].as_u64() == Some(slot as u64))
                .unwrap();
            assert_eq!(b["props"]["adept"], true, "slot {slot} is adept-only");
        }
    }

    #[test]
    fn the_lifecycle_breadcrumb_marks_the_current_step() {
        let card = mandate_card_value();
        let crumbs = of_kind(&card, "breadcrumb");
        assert_eq!(crumbs.len(), 1);
        let items = crumbs[0]["props"]["items"].as_array().unwrap();
        assert_eq!(items.len(), 4, "grant → enrol → spend → revoke");
        assert_eq!(items[1]["label"], "› Enrol", "the active step is marked");
    }

    #[test]
    fn every_button_carries_its_service_method_as_the_turn_payload() {
        let card = mandate_card_value();
        let buttons = of_kind(&card, "button");
        assert_eq!(buttons.len(), 3);
        let turns: Vec<&str> = buttons
            .iter()
            .map(|b| b["props"]["onClick"]["turn"].as_str().unwrap())
            .collect();
        assert_eq!(turns, vec![METHOD_ENROL, METHOD_SPEND, METHOD_REVOKE]);
    }

    #[test]
    fn the_card_serializes_to_parseable_json() {
        let s = mandate_card_json();
        let back: Value = serde_json::from_str(&s).expect("the card JSON parses");
        assert_eq!(back["kind"], "vstack");
        // header row, role row, breadcrumb, divider, authority, actions
        assert_eq!(back["children"].as_array().unwrap().len(), 6);
    }
}
