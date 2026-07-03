//! **THE MAIL ROOM** — the desktop face of the [`Letter Office`](crate::letter_office):
//! mail between agents, on the live World.
//!
//! Ember runs **Postmark**, a slow pen-pal mail town for AI agents (letters as markdown, a
//! twice-daily mailman, `WHITE_PAGES` / `inbox` / `outbox`). This window is dregg's own
//! post office: your INBOX (letters delivered to you), your OUTBOX (letters you have sent,
//! each Outbound one carrying a *deliver now* button that fires one ferry round as a real
//! receipted turn), and the town's MAIL-LEDGER (every letter in the town — each a cell a
//! real turn committed). A compose strip writes a new letter to a chosen correspondent as a
//! genuine send turn.
//!
//! Every letter you see IS a cell on the World: its markdown lives in the cell's heap, its
//! journey (sender · recipient · digest · status) in its slots. So the room never shows you
//! a cached list — it renders the executor's truth, re-scanned off the ledger each paint
//! ([`crate::letter_office::mailbox_of`] / [`town_letters`](crate::letter_office::town_letters)).
//!
//! ## The clobber-safe split
//!
//! Like [`super::agent_room`], this module is pure presentation plus a small gpui-free
//! model: the tab vocabulary ([`MailRoomTab`]), the per-window view state
//! ([`MailRoomState`]), the recipient-picking helpers ([`recipient_candidates`] /
//! [`default_recipient`]), and the read-only face renderers ([`render_inbox_face`] /
//! [`render_ledger_face`] / [`letter_card`]) over the [`Letter Office`](crate::letter_office)
//! reads. The desktop View owns the window dispatch, the clickable picker + tab strips, the
//! compose input, and the OUTBOX face's per-letter *deliver now* buttons (it holds the
//! `Context` the listeners need).

use gpui::{
    div, px, AnyElement, FontWeight, InteractiveElement, IntoElement, ParentElement, ScrollHandle,
    Styled,
};

use dregg_types::CellId;

use crate::deos_desktop::chrome::{
    face_row, face_section, id_short, nt_scroll_face, NT_DIM, NT_LABEL, NT_OK, NT_PANEL, NT_WARN,
};
use crate::letter_office::{is_mail_cell, LetterStatus, LetterView, MailboxView};
use crate::world::World;

/// The deterministic anchor cell the desktop hosts the Mail Room window under — a distinct
/// non-ledger sentinel (like the Agent Room's `0xA6` and the bot-surface's `0xB0`) so the
/// room opens as its OWN window keyed apart from any inspectable cell. `0xF3` — the ferry
/// (Postmark's *Ferry*, the mailman who runs the crossing).
pub fn mail_room_window_cell() -> CellId {
    CellId::from_bytes([0xF3u8; 32]) // 'F3rry'
}

/// Whether `cell` keys the Mail Room window (drives the pane title + body).
pub fn is_mail_room(cell: &CellId) -> bool {
    cell == &mail_room_window_cell()
}

/// The faces of the Mail Room — the moldable multiplicity over one post office.
#[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
pub enum MailRoomTab {
    /// The letters delivered TO the operator (their inbox).
    #[default]
    Inbox,
    /// The letters the operator has SENT (their outbox — Outbound rows carry *deliver now*).
    Outbox,
    /// The town-wide MAIL-LEDGER — every letter in the town, newest first.
    Ledger,
}

impl MailRoomTab {
    /// The tab caption the caller draws on the clickable strip.
    pub fn label(self) -> &'static str {
        match self {
            MailRoomTab::Inbox => "Inbox",
            MailRoomTab::Outbox => "Outbox",
            MailRoomTab::Ledger => "Mail-Ledger",
        }
    }

    /// Every tab, in display order — the caller iterates this to build the strip.
    pub const ALL: [MailRoomTab; 3] =
        [MailRoomTab::Inbox, MailRoomTab::Outbox, MailRoomTab::Ledger];
}

/// The per-window view state of a Mail Room — which correspondent the compose strip writes
/// to, and which face is shown. The caller holds this keyed by the room's sentinel cell;
/// `recipient: None` means "follow the default correspondent" (the most-active other
/// resident), so a fresh room always opens ready to write to whoever is most alive.
#[derive(Clone, Default)]
pub struct MailRoomState {
    /// The correspondent the compose strip addresses (the recipient of a new letter).
    pub recipient: Option<CellId>,
    /// The face on show.
    pub tab: MailRoomTab,
}

/// The candidate recipients a letter may be written to — every ordinary resident cell
/// (NOT the operator, NOT the mail plumbing), ranked most-active-first by its committed-turn
/// nonce, the id as the stable tie-break. The caller renders these as the picker strip.
pub fn recipient_candidates(world: &World, user: CellId) -> Vec<(CellId, u64)> {
    let mut v: Vec<(CellId, u64)> = world
        .ledger()
        .iter()
        .filter(|(id, _)| **id != user && !is_mail_cell(world, id))
        .map(|(id, cell)| (*id, cell.state.nonce()))
        .collect();
    v.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.as_bytes().cmp(b.0.as_bytes())));
    v
}

/// The default correspondent to address — the most-active resident that is not the operator
/// (nor the mail plumbing). `None` when the operator is the only resident (an honest answer:
/// there is no one to write to yet).
pub fn default_recipient(world: &World, user: CellId) -> Option<CellId> {
    recipient_candidates(world, user)
        .into_iter()
        .next()
        .map(|(id, _)| id)
}

/// The color a status chip wears — green for delivered (it landed), amber for outbound (it
/// awaits the ferry), dim for a draft.
fn status_color(status: LetterStatus) -> u32 {
    match status {
        LetterStatus::Delivered => NT_OK,
        LetterStatus::Outbound => NT_WARN,
        LetterStatus::Draft => NT_DIM,
    }
}

/// A short body preview — the first non-empty markdown line, trimmed, for the letter card's
/// one-glance sense of what it says (the full body opens in the letter cell's inspector).
fn body_preview(body: &str) -> String {
    let line = body
        .lines()
        .map(|l| l.trim_start_matches('#').trim())
        .find(|l| !l.is_empty())
        .unwrap_or("");
    if line.chars().count() > 72 {
        let cut: String = line.chars().take(71).collect();
        format!("{cut}…")
    } else {
        line.to_string()
    }
}

/// **A LETTER CARD** — one letter rendered read-only: its status chip + subject, the
/// from → to addresses, the sent/delivered heights, the verify-delivery tick (the committed
/// digest still anchors the body), and a one-line body preview. Returned as a bare `Div` so
/// the caller can append an affordance (the OUTBOX face welds a *deliver now* button on an
/// Outbound row); the read-only faces mount it as-is.
pub fn letter_card(l: &LetterView) -> gpui::Div {
    let chip = status_color(l.status);
    let route = format!("{}  →  {}", id_short(&l.from), id_short(&l.to));
    let when = if l.status == LetterStatus::Delivered {
        format!("sent @{} · delivered @{}", l.sent_at, l.delivered_at)
    } else {
        format!("sent @{} · awaiting the ferry", l.sent_at)
    };
    let (verify_text, verify_color) = if l.digest_matches() {
        ("digest ✓", NT_OK)
    } else {
        ("digest ✗ — content drifted", NT_WARN)
    };
    div()
        .flex()
        .flex_col()
        .gap_1()
        .p_2()
        .bg(gpui::rgb(0xffffff))
        .child(
            div()
                .flex()
                .flex_row()
                .gap_2()
                .items_center()
                .child(
                    div()
                        .px_1()
                        .text_size(px(9.0))
                        .text_color(gpui::rgb(0xffffff))
                        .bg(gpui::rgb(chip))
                        .font_weight(FontWeight::BOLD)
                        .child(l.status.label().to_uppercase()),
                )
                .child(
                    div()
                        .flex_1()
                        .text_size(px(12.0))
                        .font_weight(FontWeight::BOLD)
                        .text_color(gpui::rgb(0x101010))
                        .child(if l.subject.is_empty() {
                            "(no subject)".to_string()
                        } else {
                            l.subject.clone()
                        }),
                ),
        )
        .child(
            div()
                .flex()
                .flex_row()
                .gap_2()
                .text_size(px(10.0))
                .child(div().text_color(gpui::rgb(0x000080)).child(route))
                .child(div().flex_1().text_color(gpui::rgb(NT_DIM)).child(when))
                .child(div().text_color(gpui::rgb(verify_color)).child(verify_text)),
        )
        .child(
            div()
                .text_size(px(11.0))
                .text_color(gpui::rgb(NT_LABEL))
                .child(body_preview(&l.body)),
        )
}

/// The room's header strip — WHO this office is and its on-ledger tallies (received · sent ·
/// pending), rendered above every face. Pure presentation; the caller mounts it.
pub fn render_mailbox_header(mb: &MailboxView) -> AnyElement {
    div()
        .flex()
        .flex_col()
        .gap_1()
        .child(face_section(&format!(
            "Post office {} · the executor's account of its mail",
            id_short(&mb.owner)
        )))
        .child(face_row(
            "received",
            &format!("{} letter(s) in the inbox", mb.received),
        ))
        .child(face_row(
            "sent",
            &format!("{} sent · {} awaiting the ferry", mb.sent, mb.pending),
        ))
        .into_any_element()
}

/// The INBOX face — the letters delivered to this office, newest first. Each is a real cell
/// a receipted delivery turn moved here.
pub fn render_inbox_face(mb: &MailboxView, scroll: &ScrollHandle) -> AnyElement {
    let n = mb.inbox.len();
    let mut col = div()
        .id("mailroom-inbox")
        .bg(gpui::rgb(NT_PANEL))
        .p_2()
        .flex()
        .flex_col()
        .gap_2()
        .child(face_section(&format!("Inbox · {n} delivered letter(s)")));
    if n == 0 {
        return nt_scroll_face(
            scroll,
            col.child(face_row(
                "(empty)",
                "no letters delivered yet — the box is quiet",
            )),
        )
        .into_any_element();
    }
    for l in &mb.inbox {
        col = col.child(letter_card(l));
    }
    nt_scroll_face(scroll, col).into_any_element()
}

/// The MAIL-LEDGER face — every letter in the town, newest-sent first. The unforgeable
/// record: each row is a letter cell, its status the on-ledger truth of its journey.
pub fn render_ledger_face(town: &[LetterView], scroll: &ScrollHandle) -> AnyElement {
    let n = town.len();
    let delivered = town
        .iter()
        .filter(|l| l.status == LetterStatus::Delivered)
        .count();
    let mut col = div()
        .id("mailroom-ledger")
        .bg(gpui::rgb(NT_PANEL))
        .p_2()
        .flex()
        .flex_col()
        .gap_2()
        .child(face_section(&format!(
            "Mail-Ledger · {n} letter(s) town-wide · {delivered} delivered"
        )));
    if n == 0 {
        return nt_scroll_face(
            scroll,
            col.child(face_row(
                "(empty)",
                "no letters in the town yet — write the first one",
            )),
        )
        .into_any_element();
    }
    for l in town {
        col = col.child(letter_card(l));
    }
    nt_scroll_face(scroll, col).into_any_element()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::letter_office::send_letter;
    use crate::world::World;

    /// The recipient picker ranks other residents by nonce and never offers the operator
    /// nor the mail plumbing (offices/letters/ferry) as a correspondent.
    #[test]
    fn recipients_exclude_the_operator_and_the_mail_plumbing() {
        let mut w = World::new();
        let user = w.genesis_cell(0x33, 5_000);
        let peer = w.genesis_cell(0x44, 5_000);

        // Before any mail: the only other resident is `peer`, so it is the default.
        assert_eq!(default_recipient(&w, user), Some(peer));

        // Sending installs office + ferry + letter cells; none may become a candidate.
        send_letter(&mut w, user, peer, "hi", "hello there").unwrap();
        let cands = recipient_candidates(&w, user);
        assert!(cands.iter().all(|(id, _)| *id != user));
        assert!(
            cands.iter().all(|(id, _)| !is_mail_cell(&w, id)),
            "no office / letter / ferry cell is ever a recipient"
        );
        assert!(
            cands.iter().any(|(id, _)| *id == peer),
            "the real peer is still offered"
        );
    }

    /// The tab vocabulary is stable and its labels are the ones the strip draws.
    #[test]
    fn the_faces_are_inbox_outbox_ledger() {
        assert_eq!(MailRoomTab::ALL.len(), 3);
        assert_eq!(MailRoomTab::default(), MailRoomTab::Inbox);
        assert_eq!(MailRoomTab::Outbox.label(), "Outbox");
        assert_eq!(MailRoomTab::Ledger.label(), "Mail-Ledger");
    }
}
