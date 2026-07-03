//! # domains — the UI as a deos-view CARD (a `deos.ui.*` view-tree).
//!
//! The fourth axis of a modern starbridge-app: the binding surface as a
//! renderer-independent **card** — a serializable `deos.ui.*` element-tree. The SAME
//! tree renders three ways (native gpui pixels, a browser HTML document, a discord
//! embed) from this one piece of DATA. A starbridge-app must never depend on
//! `deos-view` (it pulls the SpiderMonkey + gpui elephants), so the app's contribution
//! is the **view-tree JSON** (this module): pure `serde_json`, no elephant.
//!
//! ## The card shape — a live custom-domain surface
//!
//! A titled column: a **status header** (the app name + a LIVE `pill` reading
//! [`VERIFICATION_STATE_SLOT`](crate::VERIFICATION_STATE_SLOT) — `PENDING` while
//! control is unproven, `VERIFIED` once DNS proves it), a lifecycle `breadcrumb`
//! (registered → bound → verified), a **"Record" `section`** surfacing the live
//! per-domain cell state (the model whose teeth are `WriteOnce(DOMAIN/OWNER/NONCE)` ·
//! `Monotonic(VERIFICATION_STATE/VERIFIED_SEQ)`), and an **"Actions" `section`** of one
//! icon+button row per lifecycle method. The button `turn` names ARE the app's method
//! vocabulary ([`METHOD_REGISTER`](crate::METHOD_REGISTER) /
//! [`METHOD_BIND`](crate::METHOD_BIND) / [`METHOD_VERIFY`](crate::METHOD_VERIFY) /
//! [`METHOD_RESOLVE`](crate::METHOD_RESOLVE)) — so the card and the cell speak the same
//! registry.

use serde_json::{Value, json};

use crate::{
    CHALLENGE_NONCE_SLOT, DOMAIN_SLOT, METHOD_BIND, METHOD_REGISTER, METHOD_RESOLVE, METHOD_VERIFY,
    OWNER_SLOT, SITE_SLOT, VERIFICATION_STATE_SLOT, VERIFIED_SEQ_SLOT,
};

/// A `deos.ui.text` node.
fn text(s: &str) -> Value {
    json!({ "kind": "text", "props": { "text": s } })
}

/// A LIVE `deos.ui.pill` node — reads `slot` immediate-mode and maps the value to a
/// word + color via `cases` (the first `{value,label,tag}` matching the slot wins).
fn pill_live(slot: usize, label: &str, tag: &str, cases: Value) -> Value {
    json!({ "kind": "pill", "props": { "text": label, "tag": tag, "slot": slot, "cases": cases } })
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

/// A `deos.ui.bind` node tagged with the model `slot` it re-reads + a label prefix and
/// a display `fmt` (`"id"` handle / `"hash"` short-hex / `"raw"` plain). `adept` hides
/// the row in the simple projection (it duplicates a friendlier signal or is a raw
/// internal numeric); revealed in the adept "see the bones" view.
fn bind(slot: usize, label: &str, fmt: &str, adept: bool) -> Value {
    json!({ "kind": "bind", "props": { "slot": slot, "label": label, "fmt": fmt, "adept": adept } })
}

/// A `deos.ui.breadcrumb` node — the lifecycle path; the `active` step is marked.
fn breadcrumb(steps: &[&str], active: usize) -> Value {
    let items: Vec<Value> = steps
        .iter()
        .enumerate()
        .map(|(i, s)| {
            let label = if i == active {
                format!("> {s}")
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

/// An action row — an `icon` + a lifecycle `button` (the verified-turn affordance).
fn action(glyph: &str, label: &str, turn: &str) -> Value {
    row(vec![icon(glyph, "accent"), button(label, turn, 0)])
}

/// **The domains card as a `deos.ui.*` view-tree** (a `serde_json::Value`).
///
/// A live custom-domain surface: a status header (the app name + a `PENDING`/`VERIFIED`
/// live pill), a lifecycle breadcrumb, a "Record" section surfacing the domain / site /
/// owner / nonce / state / seq binds, and an "Actions" section of the four
/// icon-labelled lifecycle buttons. Renderer-independent DATA.
pub fn domains_card_value() -> Value {
    json!({
        "kind": "vstack",
        "props": {},
        "children": [
            row(vec![
                text("Custom Domains"),
                pill_live(
                    VERIFICATION_STATE_SLOT as usize,
                    "PENDING",
                    "warn",
                    json!([
                        { "value": 0, "label": "PENDING",  "tag": "warn" },
                        { "value": 1, "label": "VERIFIED", "tag": "good" },
                    ]),
                ),
            ]),
            breadcrumb(&["Registered", "Bound", "Verified"], 1),
            divider(),
            section("Record", "genuine", vec![
                bind(DOMAIN_SLOT as usize, "domain . ", "hash", false),
                bind(SITE_SLOT as usize, "site . ", "id", false),
                bind(OWNER_SLOT as usize, "owner . ", "id", false),
                bind(CHALLENGE_NONCE_SLOT as usize, "challenge . ", "hash", true),
                bind(VERIFICATION_STATE_SLOT as usize, "state . ", "raw", true),
                bind(VERIFIED_SEQ_SLOT as usize, "verified seq . ", "raw", true),
            ]),
            section("Actions", "", vec![
                action("+", "Register", METHOD_REGISTER),
                action("~", "Bind",     METHOD_BIND),
                action("*", "Verify",   METHOD_VERIFY),
                action(">", "Resolve",  METHOD_RESOLVE),
            ]),
        ]
    })
}

/// **The domains card as serialized `deos.ui.*` JSON** — byte-for-byte the
/// `JSON.stringify(tree)` shape a `deos-view` renderer parses. The string a host
/// serves / embeds.
pub fn domains_card_json() -> String {
    serde_json::to_string(&domains_card_value()).expect("the domains card serializes")
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
        let card = domains_card_value();
        assert_eq!(card["kind"], "vstack");
        let texts = of_kind(&card, "text");
        assert!(texts.iter().any(|t| t["props"]["text"] == "Custom Domains"));
        let pills = of_kind(&card, "pill");
        assert_eq!(pills.len(), 1);
        // The header pill is LIVE: it reads VERIFICATION_STATE_SLOT and maps 0/1.
        assert_eq!(pills[0]["props"]["slot"], VERIFICATION_STATE_SLOT as usize);
        let cases = pills[0]["props"]["cases"].as_array().unwrap();
        assert_eq!(cases.len(), 2);
        assert_eq!(cases[0]["value"], 0);
        assert_eq!(cases[0]["label"], "PENDING");
        assert_eq!(cases[1]["value"], 1);
        assert_eq!(cases[1]["label"], "VERIFIED");
    }

    #[test]
    fn the_record_section_surfaces_the_live_cell_slots_in_order() {
        let card = domains_card_value();
        let binds = of_kind(&card, "bind");
        let slots: Vec<u64> = binds
            .iter()
            .map(|b| b["props"]["slot"].as_u64().unwrap())
            .collect();
        assert_eq!(
            slots,
            vec![
                DOMAIN_SLOT as u64,
                SITE_SLOT as u64,
                OWNER_SLOT as u64,
                CHALLENGE_NONCE_SLOT as u64,
                VERIFICATION_STATE_SLOT as u64,
                VERIFIED_SEQ_SLOT as u64,
            ]
        );
        // The devy internals (nonce / state / seq) hide by default; the human-meaningful
        // domain / site / owner stay in the simple projection.
        let adept = |slot: u64| -> bool {
            binds
                .iter()
                .find(|b| b["props"]["slot"].as_u64() == Some(slot))
                .and_then(|b| b["props"]["adept"].as_bool())
                .unwrap()
        };
        assert!(!adept(DOMAIN_SLOT as u64));
        assert!(!adept(SITE_SLOT as u64));
        assert!(!adept(OWNER_SLOT as u64));
        assert!(adept(CHALLENGE_NONCE_SLOT as u64));
        assert!(adept(VERIFICATION_STATE_SLOT as u64));
        assert!(adept(VERIFIED_SEQ_SLOT as u64));
    }

    #[test]
    fn the_lifecycle_breadcrumb_marks_the_current_step() {
        let card = domains_card_value();
        let crumbs = of_kind(&card, "breadcrumb");
        assert_eq!(crumbs.len(), 1);
        let items = crumbs[0]["props"]["items"].as_array().unwrap();
        assert_eq!(items.len(), 3);
        assert_eq!(items[1]["label"], "> Bound", "the active step is marked");
    }

    #[test]
    fn every_button_carries_its_method_as_the_turn_payload() {
        let card = domains_card_value();
        let buttons = of_kind(&card, "button");
        assert_eq!(buttons.len(), 4);
        let turns: Vec<&str> = buttons
            .iter()
            .map(|b| b["props"]["onClick"]["turn"].as_str().unwrap())
            .collect();
        assert_eq!(
            turns,
            vec![METHOD_REGISTER, METHOD_BIND, METHOD_VERIFY, METHOD_RESOLVE]
        );
    }

    #[test]
    fn the_card_serializes_to_parseable_json() {
        let s = domains_card_json();
        let back: Value = serde_json::from_str(&s).expect("the card JSON parses");
        assert_eq!(back["kind"], "vstack");
        // header row, breadcrumb, divider, record section, actions section.
        assert_eq!(back["children"].as_array().unwrap().len(), 5);
    }
}
