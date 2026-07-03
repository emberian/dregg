//! # org — the UI as a deos-view CARD (a `deos.ui.*` view-tree).
//!
//! The fourth axis of a modern starbridge-app: the app lives IN the deos world by
//! shipping its surface as a **renderer-independent card** — a serializable
//! `deos.ui.*` element-tree. The SAME tree renders three ways (native gpui in the
//! cockpit, a browser HTML document, a discord embed), all from this one piece of
//! DATA. The app's contribution is the view-tree JSON (pure `serde_json`, no
//! renderer dependency); the deos world's renderers consume it.
//!
//! ## The card shape — a live "the team, its roster, and its membership turns"
//!
//! A titled column built from the rich deos-view vocabulary:
//!
//! * a **status header** — the app name + a static row of **role-tier** `pill`s
//! naming the roles on the attenuation lattice (owner / admin / member /
//! billing / viewer), and a `breadcrumb` of the membership lifecycle
//! (Found → Invite → Accept → Transfer) with the current band marked;
//! * a **"Roster" `section`** — the KILLER VISUAL is a `gauge` bound to
//! [`MEMBER_COUNT_SLOT`](crate::MEMBER_COUNT_SLOT) over a demo team size (the
//! team filling up), plus `bind`s on the owner ([`OWNER_SLOT`](crate::OWNER_SLOT),
//! an avatar handle) and the sealed org name ([`NAME_SLOT`](crate::NAME_SLOT));
//! * an **"Audit" `section`** — the append-only membership sequence height
//! ([`SEQ_SLOT`](crate::SEQ_SLOT), the `Monotonic` audit cursor) + the sealed
//! identity commitment ([`ROOT_PUBKEY_SLOT`](crate::ROOT_PUBKEY_SLOT), adept);
//! * an **"Actions" `section`** of one `icon`+`button` row per service operation
//! (`invite` / `accept` / `change_role` / `transfer`), each carrying its `onClick`.
//!
//! The button `turn` names match the [`service`](crate::service) method vocabulary.

use serde_json::{Value, json};

use crate::service::{METHOD_ACCEPT, METHOD_CHANGE_ROLE, METHOD_INVITE, METHOD_TRANSFER};
use crate::{MEMBER_COUNT_SLOT, NAME_SLOT, OWNER_SLOT, ROOT_PUBKEY_SLOT, SEQ_SLOT};

/// The demo team size the member-count gauge fills over — the roster made visible.
pub const DEMO_TEAM_SIZE: u64 = 12;

/// A `deos.ui.text` node.
fn text(s: &str) -> Value {
    json!({ "kind": "text", "props": { "text": s } })
}

/// A static `deos.ui.pill` node — a colored badge (no live slot).
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

/// A `deos.ui.bind` node tagged with the model `slot` it re-reads + a label prefix
/// and a display `fmt` (`"id"` avatar-handle / `"hash"` short-hex / `"amount"`
/// grouped / `"raw"` plain). `adept` hides a dev-y row from the simple projection.
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
fn button(label: &str, turn: &str) -> Value {
    json!({ "kind": "button", "props": { "label": label, "onClick": { "turn": turn, "arg": 0 } } })
}

/// An action row — an `icon` + a service `button` (the verified-turn affordance).
fn action(glyph: &str, label: &str, turn: &str) -> Value {
    row(vec![icon(glyph, "accent"), button(label, turn)])
}

/// **The org card as a `deos.ui.*` view-tree** (a `serde_json::Value`).
///
/// A live team dashboard: a header (name + the role-tier pills + the membership
/// lifecycle breadcrumb), a "Roster" section whose KILLER VISUAL is the
/// member-count gauge plus the owner + sealed-name binds, an "Audit" section
/// surfacing the append-only sequence height + the sealed identity commitment, and
/// an "Actions" section of the invite / accept / change_role / transfer buttons.
/// Renderer-independent DATA. The button `turn` names are the
/// [`service`](crate::service) method symbols.
pub fn org_card_value() -> Value {
    json!({
    "kind": "vstack",
    "props": {},
    "children": [
    row(vec![text("Organization")]),
    // The five roles on the attenuation lattice (cap tiers).
    row(vec![
    pill("owner", "accent"),
    pill("admin", "good"),
    pill("member", "muted"),
    pill("billing", "muted"),
    pill("viewer", "muted"),
    ]),
    breadcrumb(&["Found", "Invite", "Accept", "Transfer"], 2),
    divider(),
    section("Roster", "genuine", vec![
    // THE KILLER VISUAL: the team filling up.
    gauge(MEMBER_COUNT_SLOT as usize, DEMO_TEAM_SIZE, "members "),
    bind(OWNER_SLOT as usize, "owner · ", "id", false),
    bind(NAME_SLOT as usize, "name · ", "hash", false),
    ]),
    section("Audit", "", vec![
    // The append-only membership sequence height (the Monotonic cursor).
    bind(SEQ_SLOT as usize, "membership seq · ", "amount", false),
    // The sealed identity commitment — a dev-y bone.
    bind(ROOT_PUBKEY_SLOT as usize, "identity · ", "hash", true),
    ]),
    section("Actions", "", vec![
    action("＋", "Invite", METHOD_INVITE),
    action("✓", "Accept", METHOD_ACCEPT),
    action("⇅", "Change role", METHOD_CHANGE_ROLE),
    action("👑", "Transfer", METHOD_TRANSFER),
    ]),
    ]
    })
}

/// **The org card as serialized `deos.ui.*` JSON** — the string a host serves /
/// embeds (`JSON.stringify(tree)` shape a `deos-view` renderer parses).
pub fn org_card_json() -> String {
    serde_json::to_string(&org_card_value()).expect("the org card serializes")
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
    fn the_card_is_a_vstack_naming_the_org() {
        let card = org_card_value();
        assert_eq!(card["kind"], "vstack");
        let texts = of_kind(&card, "text");
        assert!(texts.iter().any(|t| t["props"]["text"] == "Organization"));
    }

    #[test]
    fn the_five_role_tiers_are_named_as_static_pills() {
        let card = org_card_value();
        let pills: Vec<String> = of_kind(&card, "pill")
            .into_iter()
            .map(|p| p["props"]["text"].as_str().unwrap().to_string())
            .collect();
        assert_eq!(pills, vec!["owner", "admin", "member", "billing", "viewer"]);
    }

    #[test]
    fn the_roster_gauge_reads_the_live_member_count_slot() {
        let card = org_card_value();
        let gauges = of_kind(&card, "gauge");
        assert_eq!(gauges.len(), 1, "the killer visual: the member-count gauge");
        assert_eq!(gauges[0]["props"]["slot"], MEMBER_COUNT_SLOT as usize);
        assert_eq!(gauges[0]["props"]["max"], DEMO_TEAM_SIZE);
    }

    #[test]
    fn the_sections_surface_the_roster_then_the_audit() {
        let card = org_card_value();
        let titles: Vec<&str> = of_kind(&card, "section")
            .iter()
            .map(|s| s["props"]["title"].as_str().unwrap())
            .collect();
        assert_eq!(titles, vec!["Roster", "Audit", "Actions"]);

        let binds = of_kind(&card, "bind");
        let slots: Vec<u64> = binds
            .iter()
            .map(|b| b["props"]["slot"].as_u64().unwrap())
            .collect();
        assert_eq!(
            slots,
            vec![
                OWNER_SLOT as u64,
                NAME_SLOT as u64,
                SEQ_SLOT as u64,
                ROOT_PUBKEY_SLOT as u64,
            ],
        );
    }

    #[test]
    fn the_sealed_identity_is_marked_adept_and_the_human_terms_stay_visible() {
        let card = org_card_value();
        let adept = |slot: usize| -> bool {
            of_kind(&card, "bind")
                .iter()
                .find(|b| b["props"]["slot"].as_u64() == Some(slot as u64))
                .and_then(|b| b["props"]["adept"].as_bool())
                .unwrap()
        };
        assert!(
            adept(ROOT_PUBKEY_SLOT as usize),
            "the sealed identity commitment"
        );
        assert!(!adept(OWNER_SLOT as usize));
        assert!(!adept(SEQ_SLOT as usize));
    }

    #[test]
    fn every_button_carries_its_service_method_as_the_turn_payload() {
        let card = org_card_value();
        let buttons = of_kind(&card, "button");
        assert_eq!(buttons.len(), 4);
        let turns: Vec<&str> = buttons
            .iter()
            .map(|b| b["props"]["onClick"]["turn"].as_str().unwrap())
            .collect();
        assert_eq!(
            turns,
            vec![
                METHOD_INVITE,
                METHOD_ACCEPT,
                METHOD_CHANGE_ROLE,
                METHOD_TRANSFER
            ]
        );
    }

    #[test]
    fn the_card_serializes_to_parseable_json() {
        let s = org_card_json();
        let back: Value = serde_json::from_str(&s).expect("the card JSON parses");
        assert_eq!(back["kind"], "vstack");
        // header row, role-tier row, breadcrumb, divider, Roster, Audit, Actions.
        assert_eq!(back["children"].as_array().unwrap().len(), 7);
    }
}
