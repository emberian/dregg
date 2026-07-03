//! **The AGENT ROOM** — the desktop face of an agent-as-inhabitant.
//!
//! The desktop renders cells, documents, workflows, and the World itself — but
//! until this surface it had NO face for the one thing ADOS is *for*: an agent
//! living in the World. [`crate::agent`] already models the grounded seam (the
//! ADOS keystone: the held MANDATE, the receipted ACTIONS, the AUTHORIZATION
//! boundary — all built purely from the live [`World`], never from self-report).
//! The cockpit renders that model; the desktop should too. This is that window.
//!
//! The room answers the operator's three standing questions about a resident:
//!
//!   * **WHO lives here** — the header face: the agent cell's identity, whether
//!     its loop is backed by a real ledger cell (shown honestly when not), the
//!     balance it can spend acting, and its nonce (the executor-enforced step
//!     counter of everything it has ever committed).
//!   * **WHAT it did** — the ACTIONS face: recent cap-gated turns as the
//!     executor recorded them (receipt hash, action count, computrons metered),
//!     with a REFUSED row when the ocap guarantee fired. You are not reading the
//!     agent's diary; you are reading the executor's receipts.
//!   * **WHAT it may do** — the MANDATE and REACH faces: the attenuated cap
//!     edges it holds (adoption IS attenuation), and the projection of that
//!     mandate into legible CAN / CANNOT verbs. The CANNOT rows are the point:
//!     the boundary of the loop's reach, visible at a glance.
//!
//! ## The clobber-safe split
//!
//! Like [`super::world_explorer`], this module is pure presentation plus a small
//! gpui-free model: the tab vocabulary ([`AgentRoomTab`]), the per-window view
//! state ([`AgentRoomState`]), the resident-picking helpers ([`residents`] /
//! [`default_resident`]), and the per-tab body renderer
//! ([`render_agent_room_body`]) over a prebuilt [`AgentActivity`]. The desktop
//! View owns the window dispatch, the clickable tab strip, and the resident
//! picker strip (it holds the `Context` the listeners need).

use gpui::{
    div, px, AnyElement, FontWeight, InteractiveElement, IntoElement, ParentElement, ScrollHandle,
    Styled,
};

use dregg_types::CellId;

use crate::agent::AgentActivity;
use crate::deos_desktop::chrome::{
    face_row, face_row_color, face_section, fmt_balance, id_short, nt_scroll_face, NT_DIM, NT_OK,
    NT_PANEL, NT_WARN,
};
use crate::world::World;

/// The deterministic anchor cell the desktop hosts the Agent Room window under —
/// a distinct non-ledger sentinel (like the bot-surface's) so the room opens as
/// its OWN window keyed apart from any inspectable cell.
pub fn agent_room_window_cell() -> CellId {
    CellId::from_bytes([0xA6u8; 32]) // 'A6ent'
}

/// Whether `cell` keys the Agent Room window (drives the pane title + body).
pub fn is_agent_room(cell: &CellId) -> bool {
    cell == &agent_room_window_cell()
}

/// The faces of the Agent Room — the moldable multiplicity over one resident.
#[derive(Clone, Copy, Default, PartialEq, Eq)]
pub enum AgentRoomTab {
    /// The resident's recent cap-gated turns + receipts (the grounded seam).
    #[default]
    Actions,
    /// The held mandate — the attenuated capability edges (adoption = attenuation).
    Mandate,
    /// The authorization boundary — the CAN and (crucially) CANNOT verbs.
    Reach,
}

impl AgentRoomTab {
    /// The tab caption the caller draws on the clickable strip.
    pub fn label(self) -> &'static str {
        match self {
            AgentRoomTab::Actions => "Actions",
            AgentRoomTab::Mandate => "Mandate",
            AgentRoomTab::Reach => "Reach",
        }
    }

    /// Every tab, in display order — the caller iterates this to build the strip.
    pub const ALL: [AgentRoomTab; 3] = [
        AgentRoomTab::Actions,
        AgentRoomTab::Mandate,
        AgentRoomTab::Reach,
    ];
}

/// The per-window view state of an Agent Room — which resident is watched and
/// which face is shown. The caller holds this keyed by the room's sentinel cell;
/// `resident: None` means "follow the default resident" (the most-active cell),
/// so a fresh room always opens onto whoever is actually doing things.
#[derive(Clone, Default)]
pub struct AgentRoomState {
    pub resident: Option<CellId>,
    pub tab: AgentRoomTab,
}

/// The candidate residents, most-active-first — every ledger cell ranked by its
/// nonce (the executor's committed-turn counter), id as the stable tie-break.
/// The caller renders these as the picker strip; the operator can watch ANY cell
/// as an agent (a cell that never acts simply shows an honest empty room).
pub fn residents(world: &World) -> Vec<(CellId, u64)> {
    let mut v: Vec<(CellId, u64)> = world
        .ledger()
        .iter()
        .map(|(id, cell)| (*id, cell.state.nonce()))
        .collect();
    v.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.as_bytes().cmp(b.0.as_bytes())));
    v
}

/// The default resident to watch — the most-active cell that is not the human
/// operator (`user`); falls back to `user` when nothing else has ever acted (an
/// honest answer: the operator is the only actor so far).
pub fn default_resident(world: &World, user: CellId) -> CellId {
    residents(world)
        .into_iter()
        .find(|(id, nonce)| *id != user && *nonce > 0)
        .map(|(id, _)| id)
        .unwrap_or(user)
}

/// Render the BODY for the selected tab as a pure gpui element tree over a
/// prebuilt [`AgentActivity`] (the caller builds it from the live `World` each
/// frame — the room is always the ledger's truth, never a cached self-report).
/// The clickable tab/picker strips above this body are built by the caller.
///
/// `scroll` is the face's PERSISTENT scroll handle (the View owns it, keyed per
/// tab — see `face_scroll`); each face wraps itself in the chrome kit's
/// [`nt_scroll_face`] so it scrolls behind a real, always-visible NT scrollbar
/// and keeps its position across repaints. The handle is a plain value — the
/// module stays free of view context (the clobber-safe split holds).
pub fn render_agent_room_body(
    activity: &AgentActivity,
    tab: AgentRoomTab,
    scroll: &ScrollHandle,
) -> AnyElement {
    match tab {
        AgentRoomTab::Actions => render_actions_face(activity, scroll),
        AgentRoomTab::Mandate => render_mandate_face(activity, scroll),
        AgentRoomTab::Reach => render_reach_face(activity, scroll),
    }
}

/// The room's header strip — WHO lives here, rendered above every face: backing
/// (honest when the loop is not grounded in a live cell), spendable balance, and
/// the executor-enforced step counter. Pure presentation; the caller mounts it.
pub fn render_room_header(activity: &AgentActivity) -> AnyElement {
    let backing = if activity.backed {
        ("backed", "live ledger cell", NT_OK)
    } else {
        ("backed", "NOT BACKED — no ledger cell", NT_WARN)
    };
    div()
        .flex()
        .flex_col()
        .gap_1()
        .child(face_section(&format!(
            "Resident {} · the executor's account of it",
            activity.short
        )))
        .child(face_row_color(backing.0, backing.1, backing.2))
        .child(face_row("balance", &fmt_balance(activity.balance)))
        .child(face_row(
            "nonce",
            &format!("{} committed turns (executor-counted)", activity.nonce),
        ))
        .into_any_element()
}

// ── ACTIONS: the receipted turns — the grounded seam ─────────────────────────────

/// The ACTIONS face — the resident's recent cap-gated turns, most-recent-first,
/// as the executor recorded them. A committed turn shows its height, receipt
/// hash prefix, action count, and metered computrons; a refused one shows the
/// refusal reason in amber — the ocap guarantee firing, never faked away.
fn render_actions_face(activity: &AgentActivity, scroll: &ScrollHandle) -> AnyElement {
    let n = activity.actions.len();

    let mut col = div()
        .id("agent-room-actions")
        .bg(gpui::rgb(0x101820))
        .text_color(gpui::rgb(0x9fe0a0))
        .p_2()
        .flex()
        .flex_col()
        .gap_1()
        .child(div().text_color(gpui::rgb(0x6fc0ff)).child(format!(
            "── {} recent actions · receipts, not self-report ",
            n
        )));

    if n == 0 {
        return nt_scroll_face(
            scroll,
            col.child(div().child("(no turns yet — the room is quiet)")),
        )
        .into_any_element();
    }

    for a in &activity.actions {
        if a.committed {
            let hh: String = a
                .receipt_hash
                .map(|h| h[..4].iter().map(|b| format!("{b:02x}")).collect())
                .unwrap_or_else(|| "????????".to_string());
            let height = a
                .height
                .map(|h| format!("#{h:<4}"))
                .unwrap_or_else(|| "#?   ".to_string());
            col = col.child(div().text_size(px(11.0)).child(format!(
                "{height} receipt {hh} · {} action(s) · {}cu — {}",
                a.action_count, a.computrons, a.summary
            )));
        } else {
            col = col.child(
                div()
                    .text_size(px(11.0))
                    .text_color(gpui::rgb(0xffc060))
                    .child(format!("REFUSED — {}", a.summary)),
            );
        }
    }
    nt_scroll_face(scroll, col).into_any_element()
}

// ── MANDATE: the held capability edges ────────────────────────────────────────────

/// The MANDATE face — each capability edge the resident holds: the target cell
/// it may reach, at what rights, whether the cap is faceted (effect-restricted),
/// and its expiry height if bounded. Adoption IS attenuation, made legible.
fn render_mandate_face(activity: &AgentActivity, scroll: &ScrollHandle) -> AnyElement {
    let n = activity.mandate.len();

    let mut col = div()
        .id("agent-room-mandate")
        .bg(gpui::rgb(NT_PANEL))
        .p_2()
        .flex()
        .flex_col()
        .gap_1()
        .child(face_section(&format!(
            "Held mandate · {n} capability edge(s)"
        )));

    if n == 0 {
        return nt_scroll_face(
            scroll,
            col.child(face_row("(none)", "no held caps — the room has no reach")),
        )
        .into_any_element();
    }

    for edge in &activity.mandate {
        let facet = if edge.faceted { " · faceted" } else { "" };
        let expiry = edge
            .expires_at
            .map(|h| format!(" · expires @{h}"))
            .unwrap_or_default();
        col = col.child(
            div()
                .flex()
                .flex_row()
                .gap_1()
                .text_size(px(11.0))
                .child(
                    div()
                        .w(px(72.0))
                        .text_color(gpui::rgb(0x000080))
                        .font_weight(FontWeight::BOLD)
                        .child(format!("slot {}", edge.slot)),
                )
                .child(div().w(px(96.0)).child(id_short(&edge.target)))
                .child(
                    div()
                        .flex_1()
                        .text_color(gpui::rgb(NT_DIM))
                        .child(format!("{}{facet}{expiry}", edge.rights_label())),
                ),
        );
    }
    nt_scroll_face(scroll, col).into_any_element()
}

// ── REACH: the authorization boundary — CAN and CANNOT ───────────────────────────

/// The REACH face — the mandate projected into legible verbs: green CAN rows and
/// amber CANNOT rows, each with its basis. The CANNOT rows are the edge of the
/// loop's reach — the answer to "what is this resident unable to touch?", read
/// off the real cap-graph rather than asserted.
fn render_reach_face(activity: &AgentActivity, scroll: &ScrollHandle) -> AnyElement {
    let permitted = activity
        .authorizations
        .iter()
        .filter(|a| a.permitted)
        .count();
    let denied = activity.authorizations.len() - permitted;

    let mut col = div()
        .id("agent-room-reach")
        .bg(gpui::rgb(NT_PANEL))
        .p_2()
        .flex()
        .flex_col()
        .gap_1()
        .child(face_section(&format!(
            "Authorization boundary · {permitted} CAN · {denied} CANNOT"
        )));

    if activity.authorizations.is_empty() {
        return nt_scroll_face(
            scroll,
            col.child(face_row("(none)", "no verbs projected — empty mandate")),
        )
        .into_any_element();
    }

    for auth in &activity.authorizations {
        let (verdict, color) = if auth.permitted {
            ("CAN", NT_OK)
        } else {
            ("CANNOT", NT_WARN)
        };
        col = col.child(
            div()
                .flex()
                .flex_row()
                .gap_1()
                .text_size(px(11.0))
                .child(
                    div()
                        .w(px(64.0))
                        .text_color(gpui::rgb(color))
                        .font_weight(FontWeight::BOLD)
                        .child(verdict),
                )
                .child(div().w(px(110.0)).child(auth.verb))
                .child(
                    div()
                        .flex_1()
                        .text_color(gpui::rgb(NT_DIM))
                        .child(auth.note.clone()),
                ),
        );
    }
    nt_scroll_face(scroll, col).into_any_element()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The resident ranking is nonce-descending with the id tie-break, and the
    /// default resident skips the human operator unless nobody else ever acted.
    #[test]
    fn default_resident_prefers_the_most_active_non_user() {
        let (world, anchors) = crate::world::demo_world();
        let [_treasury, _service, user] = anchors;

        // The demo world's genesis commits REAL seed turns, so a fresh desktop
        // already has non-operator actors — the default resident is the busiest
        // of them (never the operator while someone else is acting).
        let def = default_resident(&world, user);
        assert_ne!(def, user);

        let ranked = residents(&world);
        let top_non_user_nonce = ranked
            .iter()
            .filter(|(id, _)| *id != user)
            .map(|(_, n)| *n)
            .max()
            .expect("demo world has non-user cells");
        let def_nonce = ranked.iter().find(|(id, _)| *id == def).unwrap().1;
        assert_eq!(def_nonce, top_non_user_nonce);
        assert!(def_nonce > 0, "the default resident has actually acted");

        // The ranking covers every ledger cell (a picker over the whole census).
        assert_eq!(ranked.len(), world.cell_count());
    }
}
