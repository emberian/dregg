//! # guard — the UI as a deos-view CARD (a `deos.ui.*` view-tree, AX4).
//!
//! The fourth axis of a modern starbridge-app: the app lives IN the deos world by
//! shipping its surface as a **renderer-independent card** — a serializable
//! `deos.ui.*` element-tree (`deos_view::ViewNode`). The SAME tree renders three ways
//! (native gpui pixels, a browser-loadable HTML document, a discord embed) — all from
//! this one piece of DATA. A starbridge-app must never depend on `deos-view` (it pulls
//! the SpiderMonkey + gpui elephants and is a standalone workspace), so the app's
//! contribution is the **view-tree JSON** (this module): pure `serde_json`.
//!
//! ## The card shape — a rich, live SUBJECT-ACCOUNT surface
//!
//! A titled column so the abuse-governance story — *an anonymous subject held to a
//! RATE-BOUNDED, GOVERNANCE-STANDING'd budget* — is VISIBLE at a glance:
//!
//!   - a **status header** — the app name + a LIVE `pill` ([`status_pill`]) reading
//!     [`STANDING_SLOT`](crate::STANDING_SLOT) and naming the account standing as a
//!     WORD (`GOOD` / `FLAGGED` / `SUSPENDED`);
//!   - a **"Budget" `section`** — a `gauge` bound to
//!     [`CONSUMED_SLOT`](crate::CONSUMED_SLOT) over the granted ceiling (the killer
//!     visual: it FILLS as the subject spends its budget and is FULL the instant the
//!     ceiling is reached — the in-band refusal made legible), plus `bind`s on the
//!     subject SCOPE, the consumed counter, the ceiling, and the standing;
//!   - an **"Actions" `section`** — one `icon`+`button` row per method: the subject's
//!     `consume` / `view`, and the GOVERNANCE `set_standing` (the takedown), each
//!     carrying its `onClick = { turn, arg }`.
//!
//! The button `turn` names match the [`service`](crate::service) method vocabulary so
//! the card and the service cell speak the same abuse-governance vocabulary.

use serde_json::{Value, json};

use crate::service::{METHOD_CONSUME, METHOD_SET_STANDING, METHOD_VIEW};
use crate::{
    CEILING_SLOT, CONSUMED_SLOT, STANDING_FLAGGED, STANDING_SLOT, STANDING_SUSPENDED, SUBJECT_SLOT,
};

/// The budget gauge's denominator — the granted ceiling a representative account
/// carries (the [`register_deos`](crate::register_deos) seed grants `ceiling = 8`),
/// so a fully-spent account FILLS the gauge.
const BUDGET_GAUGE_MAX: u64 = 8;

/// A `deos.ui.text` node.
fn text(s: &str) -> Value {
    json!({ "kind": "text", "props": { "text": s } })
}

/// A LIVE `deos.ui.pill` node — reads `slot` immediate-mode and maps the value to a
/// word + color via `cases` (the first `{value,label,tag}` matching the slot wins).
fn pill_live(slot: u8, label: &str, tag: &str, cases: Value) -> Value {
    json!({ "kind": "pill", "props": { "text": label, "tag": tag, "slot": slot, "cases": cases } })
}

/// A `deos.ui.icon` node — a glyph indicator tinted by `tag`.
fn icon(glyph: &str, tag: &str) -> Value {
    json!({ "kind": "icon", "props": { "glyph": glyph, "tag": tag } })
}

/// A `deos.ui.divider` node.
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
/// and a display `fmt`.
fn bind(slot: u8, label: &str, fmt: &str, adept: bool) -> Value {
    json!({ "kind": "bind", "props": { "slot": slot, "label": label, "fmt": fmt, "adept": adept } })
}

/// A `deos.ui.gauge` node — a bound progress bar (`slot_value / max`, immediate-mode
/// read of the LIVE slot off the ledger).
fn gauge(slot: u8, max: u64, label: &str) -> Value {
    json!({ "kind": "gauge", "props": { "slot": slot, "max": max, "label": label } })
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

/// The account's representative status `pill` — the live standing badge named as a
/// WORD, reading [`STANDING_SLOT`](crate::STANDING_SLOT):
///
///   - `GOOD` (`good`) — the conservative default, served under the full ceiling;
///   - `FLAGGED` (`warn`) — under review, tighter tier;
///   - `SUSPENDED` (`bad`) — taken down, effective ceiling zero.
///
/// A born account reads standing `0` (`good`), so the card surfaces `GOOD`; a
/// governance `set_standing` flips it live.
fn status_pill() -> Value {
    pill_live(
        STANDING_SLOT,
        "GOOD",
        "good",
        json!([
            { "value": STANDING_FLAGGED, "label": "FLAGGED", "tag": "warn" },
            { "value": STANDING_SUSPENDED, "label": "SUSPENDED", "tag": "bad" },
        ]),
    )
}

/// **The guard card as a `deos.ui.*` view-tree** (a `serde_json::Value`).
///
/// A rich, live subject-account surface: a status header (name + [`GOOD`](status_pill)
/// standing pill), a "Budget" section surfacing the LIVE consume gauge
/// (`consumed / ceiling` — the in-band ceiling made visible) and the subject /
/// consumed / ceiling / standing binds, and an "Actions" section of the subject's
/// consume + view and the GOVERNANCE set_standing (the takedown). The button `turn`
/// names are the [`service`](crate::service) method symbols.
pub fn guard_card_value() -> Value {
    json!({
        "kind": "vstack",
        "props": {},
        "children": [
            row(vec![text("Guard · Subject Account"), status_pill()]),
            divider(),
            section("Budget", "genuine", vec![
                gauge(CONSUMED_SLOT, BUDGET_GAUGE_MAX, "quota used "),
                bind(SUBJECT_SLOT,  "subject · ", "id", false),
                bind(CONSUMED_SLOT, "consumed · ", "raw", false),
                bind(CEILING_SLOT,  "ceiling · ", "raw", false),
                bind(STANDING_SLOT, "standing · ", "raw", true),
            ]),
            section("Actions", "", vec![
                action("→", "Consume",  METHOD_CONSUME),
                action("👁", "View",     METHOD_VIEW),
                action("⊘", "Set standing", METHOD_SET_STANDING),
            ]),
        ]
    })
}

/// **The guard card as serialized `deos.ui.*` JSON** — the string a host serves /
/// embeds (parsed by `deos_view::parse_view_tree`).
pub fn guard_card_json() -> String {
    serde_json::to_string(&guard_card_value()).expect("the guard card serializes")
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
    fn the_card_is_a_vstack_with_a_named_header_and_a_live_standing_pill() {
        let card = guard_card_value();
        assert_eq!(card["kind"], "vstack");
        let texts = of_kind(&card, "text");
        assert!(
            texts
                .iter()
                .any(|t| t["props"]["text"] == "Guard · Subject Account"),
            "the header names the app"
        );
        let pills = of_kind(&card, "pill");
        assert_eq!(pills.len(), 1);
        assert_eq!(
            pills[0]["props"]["text"], "GOOD",
            "the static fallback word"
        );
        assert_eq!(pills[0]["props"]["tag"], "good");
        assert_eq!(pills[0]["props"]["slot"], STANDING_SLOT);
        let cases = pills[0]["props"]["cases"].as_array().unwrap();
        assert_eq!(cases.len(), 2, "the flagged + suspended edges");
        assert_eq!(cases[0]["value"], STANDING_FLAGGED);
        assert_eq!(cases[1]["value"], STANDING_SUSPENDED);
        assert_eq!(cases[1]["tag"], "bad");
    }

    #[test]
    fn the_budget_gauge_reads_the_live_consumed_over_the_ceiling() {
        let card = guard_card_value();
        let gauges = of_kind(&card, "gauge");
        assert_eq!(gauges.len(), 1, "the budget gauge (consumed / ceiling)");
        assert_eq!(gauges[0]["props"]["slot"], CONSUMED_SLOT);
        assert_eq!(gauges[0]["props"]["max"], BUDGET_GAUGE_MAX);
    }

    #[test]
    fn the_binds_surface_the_scope_meter_ceiling_and_standing() {
        let card = guard_card_value();
        let binds = of_kind(&card, "bind");
        let slots: Vec<u64> = binds
            .iter()
            .map(|b| b["props"]["slot"].as_u64().unwrap())
            .collect();
        assert_eq!(
            slots,
            vec![
                SUBJECT_SLOT as u64,
                CONSUMED_SLOT as u64,
                CEILING_SLOT as u64,
                STANDING_SLOT as u64,
            ]
        );
    }

    #[test]
    fn every_button_carries_its_service_method_as_the_turn_payload() {
        let card = guard_card_value();
        let buttons = of_kind(&card, "button");
        assert_eq!(buttons.len(), 3);
        let turns: Vec<&str> = buttons
            .iter()
            .map(|b| b["props"]["onClick"]["turn"].as_str().unwrap())
            .collect();
        assert_eq!(
            turns,
            vec![METHOD_CONSUME, METHOD_VIEW, METHOD_SET_STANDING]
        );
    }

    #[test]
    fn the_card_serializes_to_parseable_json() {
        let s = guard_card_json();
        let back: Value = serde_json::from_str(&s).expect("the card JSON parses");
        assert_eq!(back["kind"], "vstack");
        // header row, divider, budget section, actions section
        assert_eq!(back["children"].as_array().unwrap().len(), 4);
    }
}
