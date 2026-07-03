//! **MY DREGG COMPUTERS** — the desktop face of *have a Dregg Computer*: the
//! vats you can reach, and the one you are attached to, reflected live.
//!
//! A Dregg Computer is a **vat**: a private, always-there computer that happens
//! to live in the cloud but belongs to *you* — technically a DreggNet
//! `ServerFleet` persistent server whose identity is a content-addressed CELL
//! (`ServerRecord.cell_id`), admitted behind a funded lease that reads your
//! REAL reserve, scoped to you by a `vat:<cell-id>` capability, and checkable
//! against your own trust anchor because every action it takes is receipted
//! (DREGG-COMPUTER.md). This window is where a starbridge answers "which
//! computers are mine, and what is mine doing right now?":
//!
//!   * **COMPUTERS** — the roster off the gateway's designed `GET /v1/vats`
//!     ([`crate::client::VATS_ROUTE`], the NAMED SEAM): each vat's name, its
//!     cell identity, its lifecycle posture (running · sleeping-as-a-committed-
//!     checkpoint · created-but-unfunded), the funded-lease truth, the witness
//!     discipline it runs, and — for a reachable one — CONNECT.
//!   * **CONNECTION** — the attached vat reflected over the SAME wire contract
//!     the `--node <url>` remote path speaks ([`crate::client::NodeClient`] +
//!     [`crate::live_node`]): its `/status` liveness, and its REMOTE cells —
//!     your stuff, on your computer, read live, never cached self-report.
//!   * **RECEIPTS** — the vat's receipt nervous system: the snapshot tail plus
//!     (against a live endpoint) the SSE stream drained beat-by-beat into the
//!     dedup-and-resume [`ReceiptFeed`], so the chronicle advances while you
//!     watch. Receipts are what make the computer un-lie-able — this face is
//!     the point of the product.
//!
//! ## Honest v0
//!
//! The roster source is named on the glass: without a gateway it is the
//! [`crate::client::mock::vats`] FIXTURE (the same wire shape, no network) and
//! connecting attaches the mock backend; with `DREGG_GATEWAY_URL` set it reads
//! the live `GET /v1/vats` and connects to the vat's real endpoint over the
//! proven HTTP+SSE path. Nothing here fakes liveness: an unreachable endpoint
//! surfaces its error, a fixture names itself a fixture, and the verify-a-
//! receipt-against-your-own-anchor affordance is the named next increment (the
//! wire rows already carry the hashes it will check).
//!
//! ## The clobber-safe split
//!
//! Like [`super::agent_room`] / [`super::mail_room`], this module is pure
//! presentation plus a small gpui-free model: the tab vocabulary
//! ([`DreggComputersTab`]), the per-window view state ([`DreggComputersState`]),
//! the roster model ([`VatDirectory`] — fixture or live gateway, honestly
//! sourced), the attach model ([`VatLink`] — snapshot + stream over one
//! `NodeClient`), and the read-only face renderers. The desktop View owns the
//! window dispatch, the tab strip, and the per-vat CONNECT buttons (it holds
//! the `Context` the listeners need).

use gpui::{
    div, px, AnyElement, FontWeight, InteractiveElement, IntoElement, ParentElement, ScrollHandle,
    Styled,
};

use dregg_types::CellId;

use crate::client::{LiveNode, NodeClient, ReceiptStreamHandle};
use crate::deos_desktop::chrome::{
    face_row, face_row_color, face_section, fmt_balance, nt_scroll_face, NT_DIM, NT_LABEL, NT_OK,
    NT_PANEL, NT_WARN,
};
use crate::live_node::ReceiptFeed;
use crate::model::{short_id, ReceiptEvent, VatEntry};

/// The env var naming a LIVE DreggNet gateway to read the vat roster from
/// (`GET /v1/vats` against it, with the account credential when one is held).
/// Unset ⇒ the fixture roster, named honestly on the glass — the same
/// env-gated-seam discipline as the Matrix Room's `DEOS_HOMESERVER_URL`.
pub const GATEWAY_ENV: &str = "DREGG_GATEWAY_URL";

/// The receipt-feed retention — the visible tail of the vat's chronicle.
const FEED_CAP: usize = 256;

/// The deterministic anchor cell the desktop hosts the My Dregg Computers
/// window under — a distinct non-ledger sentinel (like the Agent Room's `0xA6`
/// and the Mail Room's `0xF3`) so the surface opens as its OWN window keyed
/// apart from any inspectable cell. `0xDC` — Dregg Computer.
pub fn dregg_computers_window_cell() -> CellId {
    CellId::from_bytes([0xDCu8; 32]) // 'DreggComputer'
}

/// Whether `cell` keys the My Dregg Computers window (drives title + body).
pub fn is_dregg_computers(cell: &CellId) -> bool {
    cell == &dregg_computers_window_cell()
}

/// The faces of the surface — the moldable multiplicity over one fleet.
#[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
pub enum DreggComputersTab {
    /// The roster — every vat you can reach, with CONNECT on the reachable ones.
    #[default]
    Computers,
    /// The attached vat reflected live: `/status` + its remote cells.
    Connection,
    /// The attached vat's receipt stream — the un-lie-able chronicle, advancing.
    Receipts,
}

impl DreggComputersTab {
    /// The tab caption the caller draws on the clickable strip.
    pub fn label(self) -> &'static str {
        match self {
            DreggComputersTab::Computers => "Computers",
            DreggComputersTab::Connection => "Connection",
            DreggComputersTab::Receipts => "Receipts",
        }
    }

    /// Every tab, in display order — the caller iterates this to build the strip.
    pub const ALL: [DreggComputersTab; 3] = [
        DreggComputersTab::Computers,
        DreggComputersTab::Connection,
        DreggComputersTab::Receipts,
    ];
}

/// The per-window view state — which face is shown. The caller holds this keyed
/// by the surface's sentinel cell. (The ATTACHMENT is deliberately NOT here: the
/// link is to a remote computer, not to a window, so it lives on the desktop and
/// survives the window closing — your computer stays yours with the lid shut.)
#[derive(Clone, Default)]
pub struct DreggComputersState {
    pub tab: DreggComputersTab,
}

// ═══════════════════════════════════════════════════════════════════════════════
// THE ROSTER — VatDirectory: which computers exist, honestly sourced
// ═══════════════════════════════════════════════════════════════════════════════

/// Where a [`VatDirectory`] roster came from — surfaced on the glass, always.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DirectorySource {
    /// The in-process fixture ([`crate::client::mock::vats`]) — the same wire
    /// shape the gateway will return, no network. Connecting a fixture vat
    /// attaches the mock backend (real data shapes, honestly labeled).
    Fixture,
    /// A live gateway at this base URL — the roster is `GET /v1/vats` truth.
    Gateway(String),
}

/// The vat roster + its provenance. gpui-free; built once at desktop
/// construction ([`VatDirectory::discover`]) and re-readable on demand.
pub struct VatDirectory {
    /// The vats, as the source reported them.
    pub vats: Vec<VatEntry>,
    /// Where the roster came from (fixture vs live gateway) — never hidden.
    pub source: DirectorySource,
    /// A gateway read failure, surfaced instead of silently falling back to
    /// the fixture (an empty-but-erring live roster must not masquerade as a
    /// healthy fixture one).
    pub error: Option<String>,
}

impl VatDirectory {
    /// Discover the roster: `DREGG_GATEWAY_URL` set ⇒ read the LIVE gateway
    /// (`GET /v1/vats`); unset ⇒ the fixture. The one env-gated seam.
    pub fn discover() -> Self {
        match std::env::var(GATEWAY_ENV) {
            Ok(url) if !url.trim().is_empty() => Self::from_gateway(url.trim().to_string()),
            _ => Self::fixture(),
        }
    }

    /// The fixture roster — [`crate::client::mock::vats`], named as such.
    pub fn fixture() -> Self {
        VatDirectory {
            vats: NodeClient::mock().vats().unwrap_or_default(),
            source: DirectorySource::Fixture,
            error: None,
        }
    }

    /// Read the roster from a live gateway (`GET /v1/vats` at `url`). A failed
    /// read keeps the gateway as the named source and carries the error — it
    /// does NOT quietly fall back to the fixture.
    pub fn from_gateway(url: String) -> Self {
        match NodeClient::http(url.clone()).vats() {
            Ok(vats) => VatDirectory {
                vats,
                source: DirectorySource::Gateway(url),
                error: None,
            },
            Err(e) => VatDirectory {
                vats: Vec::new(),
                source: DirectorySource::Gateway(url),
                error: Some(e.to_string()),
            },
        }
    }

    /// Find a vat by its cell id.
    pub fn vat(&self, cell_id: &str) -> Option<&VatEntry> {
        self.vats.iter().find(|v| v.cell_id == cell_id)
    }

    /// The backend a CONNECT on `vat` attaches — the seam where fixture and
    /// live part ways, decided by the roster's source (never by guessing):
    ///
    ///   * fixture roster ⇒ the `Mock` backend (real wire shapes, no socket);
    ///   * gateway roster ⇒ HTTP at the vat's real endpoint — the SAME
    ///     `NodeClient::http` the `--node <url>` remote path proves out;
    ///   * a gateway vat with NO endpoint refuses honestly (nothing listens —
    ///     it is asleep as a committed checkpoint, or was never funded).
    pub fn client_for(&self, vat: &VatEntry) -> Result<NodeClient, String> {
        match &self.source {
            DirectorySource::Fixture => Ok(NodeClient::mock()),
            DirectorySource::Gateway(_) => {
                match vat.endpoint.as_deref().filter(|e| !e.is_empty()) {
                    Some(url) => Ok(NodeClient::http(url)),
                    None => Err(format!(
                        "'{}' has no reachable endpoint — it is {} (wake it first)",
                        vat.name,
                        if vat.state.is_empty() {
                            "not running"
                        } else {
                            &vat.state
                        }
                    )),
                }
            }
        }
    }

    /// The one-line provenance caption the header wears.
    pub fn describe(&self) -> String {
        match &self.source {
            DirectorySource::Fixture => format!(
                "{} computer(s) · FIXTURE roster — live seam: GET {} (set {})",
                self.vats.len(),
                crate::client::VATS_ROUTE,
                GATEWAY_ENV
            ),
            DirectorySource::Gateway(url) => format!(
                "{} computer(s) · live gateway {url}{}",
                self.vats.len(),
                crate::client::VATS_ROUTE
            ),
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// THE ATTACH — VatLink: one computer, reflected over the proven wire path
// ═══════════════════════════════════════════════════════════════════════════════

/// A live attachment to ONE Dregg Computer — the composition of the pieces the
/// `--node <url>` remote path already proves: a [`NodeClient`] at the vat's
/// endpoint, the blocking snapshot reads (`/status`, `/api/cells`,
/// `/api/receipts`), and — against a live endpoint — the background SSE reader
/// whose records the desktop's pulse drains into the dedup-and-resume
/// [`ReceiptFeed`] each beat. gpui-free; every field the faces render is data.
pub struct VatLink {
    /// Which computer this is (the roster row we attached).
    pub vat: VatEntry,
    /// The wire backend (mock for a fixture vat; HTTP at the real endpoint).
    pub client: NodeClient,
    /// The vat's `/status`, when the snapshot read succeeded.
    pub status: Option<crate::model::NodeStatus>,
    /// The vat's remote cells — YOUR cells, on YOUR computer, read live.
    pub cells: Vec<crate::model::CellListEntry>,
    /// The receipt tail: seeded from the snapshot, advanced by the stream.
    pub feed: ReceiptFeed,
    /// A connect/read failure, surfaced on the Connection face (never hidden).
    pub error: Option<String>,
    /// The background SSE reader (live endpoints only; `None` for mock /
    /// no-`live-node` builds — the feed then holds the snapshot tail).
    stream: Option<ReceiptStreamHandle>,
}

impl VatLink {
    /// Attach `client` to `vat`: take the snapshot (status + cells + receipt
    /// tail) and, when something real is listening, start the SSE reader. An
    /// unreachable endpoint comes back as a link CARRYING its error — the
    /// Connection face shows the truth rather than the desktop pretending the
    /// attach never happened.
    pub fn connect_with(vat: VatEntry, client: NodeClient) -> VatLink {
        let (status, error) = match client.status() {
            Ok(s) => (Some(s), None),
            Err(e) => (None, Some(format!("unreachable — {e}"))),
        };
        let cells = client.cells().unwrap_or_default();
        let mut feed = ReceiptFeed::new(FEED_CAP);
        if let Ok(evs) = client.receipts() {
            for ev in evs {
                feed.ingest(ev);
            }
        }
        // Only a live, answering endpoint gets the stream tap (the reader
        // auto-reconnects from the feed's cursor; the mock has no socket).
        let stream = if error.is_none() {
            LiveNode::new(client.clone()).connect_stream()
        } else {
            None
        };
        VatLink {
            vat,
            client,
            status,
            cells,
            feed,
            error,
            stream,
        }
    }

    /// Drain every receipt the SSE reader delivered since the last beat into
    /// the feed (dedup + resume-cursor advance). Returns how many were NEW —
    /// the desktop's pulse turns each into a repaint. Zero without a stream.
    pub fn pump(&mut self) -> usize {
        let Some(stream) = &self.stream else {
            return 0;
        };
        let records = stream.drain();
        if records.is_empty() {
            return 0;
        }
        self.feed.ingest_records(records)
    }

    /// Whether a live SSE reader is running (vs the snapshot-only tail).
    pub fn streaming(&self) -> bool {
        self.stream.is_some()
    }

    /// The one-line attachment caption ("'mybox' via http://… · streaming").
    pub fn describe(&self) -> String {
        format!(
            "'{}' via {} · {}",
            self.vat.name,
            self.client.describe(),
            if self.streaming() {
                "receipts streaming"
            } else {
                "snapshot"
            }
        )
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// PURE PRESENTATION — the faces (inert elements; the View welds the buttons)
// ═══════════════════════════════════════════════════════════════════════════════

/// The color a lifecycle chip wears — green for running (it answers), amber for
/// sleeping (it IS its committed checkpoint), dim for anything unlaunched.
pub fn vat_state_color(state: &str) -> u32 {
    match state {
        "running" => NT_OK,
        "sleeping" => NT_WARN,
        _ => NT_DIM,
    }
}

/// The one-line roster text for a vat — the bake witness twin of [`vat_card`]
/// (a headless test reads THIS to assert the card carries the rental truths).
pub fn vat_card_text(v: &VatEntry) -> String {
    format!(
        "{} · {} · {} · {} period(s) · {} · {} · vat:{}",
        if v.name.is_empty() {
            "(unnamed)"
        } else {
            &v.name
        },
        if v.state.is_empty() {
            "unknown"
        } else {
            &v.state
        },
        if v.funded { "funded" } else { "UNFUNDED" },
        v.paid_periods,
        if v.witness_mode.is_empty() {
            "full"
        } else {
            &v.witness_mode
        },
        match (&v.endpoint, &v.checkpoint_root) {
            (Some(url), _) => format!("endpoint {url}"),
            (None, Some(root)) => format!("checkpoint {}", short_id(root)),
            (None, None) => "no endpoint".to_string(),
        },
        short_id(&v.cell_id),
    )
}

/// **A COMPUTER CARD** — one vat rendered read-only: the lifecycle chip + name,
/// the cell identity + the `vat:<id>` capability scope that reaches exactly it,
/// the funded-lease + settle truths, the witness discipline, and where it is
/// reachable (endpoint) or committed (checkpoint root). Returned as a bare
/// `Div` so the caller can append the CONNECT affordance; read-only callers
/// mount it as-is — the [`super::mail_room::letter_card`] pattern.
pub fn vat_card(v: &VatEntry, attached: bool) -> gpui::Div {
    let chip = vat_state_color(&v.state);
    let mode = if v.witness_mode.is_empty() {
        "full"
    } else {
        v.witness_mode.as_str()
    };
    let lease = format!(
        "{} · {} period(s) settled · witness {}",
        if v.funded {
            "funded lease"
        } else {
            "UNFUNDED — will not launch"
        },
        v.paid_periods,
        mode,
    );
    let lease_color = if v.funded { NT_LABEL } else { NT_WARN };
    let whereabouts = match (&v.endpoint, &v.checkpoint_root) {
        (Some(url), _) => format!("endpoint {url}"),
        (None, Some(root)) => format!("asleep as its committed root {}", short_id(root)),
        (None, None) => "no endpoint yet".to_string(),
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
                        .child(if v.state.is_empty() {
                            "UNKNOWN".to_string()
                        } else {
                            v.state.to_uppercase()
                        }),
                )
                .child(
                    div()
                        .flex_1()
                        .text_size(px(12.0))
                        .font_weight(FontWeight::BOLD)
                        .text_color(gpui::rgb(0x101010))
                        .child(if v.name.is_empty() {
                            "(unnamed)".to_string()
                        } else {
                            v.name.clone()
                        }),
                )
                .when_attached_chip(attached),
        )
        .child(
            div()
                .flex()
                .flex_row()
                .gap_2()
                .text_size(px(10.0))
                .child(
                    div()
                        .text_color(gpui::rgb(0x000080))
                        .child(format!("cell {}", short_id(&v.cell_id))),
                )
                .child(
                    div()
                        .text_color(gpui::rgb(NT_DIM))
                        .child(format!("cap vat:{}", short_id(&v.cell_id))),
                )
                .child(
                    div()
                        .flex_1()
                        .text_color(gpui::rgb(NT_DIM))
                        .child(whereabouts),
                ),
        )
        .child(
            div()
                .text_size(px(10.0))
                .text_color(gpui::rgb(lease_color))
                .child(lease),
        )
}

/// A tiny fluent helper so [`vat_card`] can mark the attached row without the
/// caller re-deriving which card got the link. (An extension trait keeps the
/// card builder one readable chain.)
trait AttachedChip {
    fn when_attached_chip(self, attached: bool) -> Self;
}

impl AttachedChip for gpui::Div {
    fn when_attached_chip(self, attached: bool) -> Self {
        if !attached {
            return self;
        }
        self.child(
            div()
                .px_1()
                .text_size(px(9.0))
                .text_color(gpui::rgb(0xffffff))
                .bg(gpui::rgb(NT_OK))
                .font_weight(FontWeight::BOLD)
                .child("ATTACHED"),
        )
    }
}

/// The surface's header strip — the roster provenance (fixture vs live gateway,
/// never hidden) and the current attachment, rendered above every face.
pub fn render_directory_header(dir: &VatDirectory, link: Option<&VatLink>) -> AnyElement {
    let attach_line = match link {
        Some(l) => l.describe(),
        None => "not attached — connect a computer below".to_string(),
    };
    let attach_color = if link.is_some() { NT_OK } else { NT_DIM };
    div()
        .flex()
        .flex_col()
        .gap_1()
        .child(face_section("My Dregg Computers · yours, and un-lie-able"))
        .child(face_row("roster", &dir.describe()))
        .child(face_row_color("attached", &attach_line, attach_color))
        .into_any_element()
}

/// The CONNECTION face — the attached vat reflected live over the wire
/// contract: `/status` liveness + producer truth, then the REMOTE cells (your
/// stuff on your computer). Unattached, it says so; a carried error shows amber.
pub fn render_connection_face(link: Option<&VatLink>, scroll: &ScrollHandle) -> AnyElement {
    let mut col = div()
        .id("dregg-computers-connection")
        .bg(gpui::rgb(NT_PANEL))
        .p_2()
        .flex()
        .flex_col()
        .gap_1();

    let Some(link) = link else {
        col = col.child(face_section("Connection")).child(face_row(
            "(none)",
            "not attached — pick a computer on the Computers face and connect",
        ));
        return nt_scroll_face(scroll, col).into_any_element();
    };

    col = col.child(face_section(&format!("Connection · {}", link.describe())));
    if let Some(err) = &link.error {
        col = col.child(face_row_color("error", err, NT_WARN));
    }
    match &link.status {
        Some(s) => {
            let health_color = if s.healthy { NT_OK } else { NT_WARN };
            col = col
                .child(face_row_color(
                    "healthy",
                    if s.healthy { "yes" } else { "DOWN" },
                    health_color,
                ))
                .child(face_row(
                    "producer",
                    &format!(
                        "{}{}",
                        s.state_producer,
                        if s.lean_producer {
                            " (verified semantics)"
                        } else {
                            ""
                        }
                    ),
                ))
                .child(face_row("height", &s.latest_height.to_string()))
                .child(face_row("peers", &s.peer_count.to_string()));
        }
        None => {
            col = col.child(face_row(
                "status",
                "(no /status — the endpoint never answered)",
            ));
        }
    }

    col = col.child(face_section(&format!(
        "Remote cells · {} — yours, on your computer",
        link.cells.len()
    )));
    if link.cells.is_empty() {
        col = col.child(face_row("(empty)", "no cells reflected"));
    }
    let cap = 24usize;
    for entry in link.cells.iter().take(cap) {
        col = col.child(
            div()
                .flex()
                .flex_row()
                .gap_1()
                .text_size(px(11.0))
                .child(
                    div()
                        .w(px(96.0))
                        .text_color(gpui::rgb(0x000080))
                        .font_weight(FontWeight::BOLD)
                        .child(short_id(&entry.id)),
                )
                .child(div().flex_1().child(fmt_balance(entry.balance)))
                .child(
                    div()
                        .w(px(56.0))
                        .text_color(gpui::rgb(NT_DIM))
                        .child(format!("n{}", entry.nonce)),
                )
                .child(
                    div()
                        .w(px(64.0))
                        .text_color(gpui::rgb(NT_DIM))
                        .child(format!("{} caps", entry.capability_count)),
                ),
        );
    }
    if link.cells.len() > cap {
        col = col.child(face_row(
            "…",
            &format!("{} more cells", link.cells.len() - cap),
        ));
    }
    nt_scroll_face(scroll, col).into_any_element()
}

/// One receipt-stream row, exactly as painted — the bake witness twin (headless
/// tests assert "the feed's row N carries THIS receipt" as plain text).
pub fn receipt_row_text(ev: &ReceiptEvent) -> String {
    format!(
        "#{:<4} h{} receipt {} · {} · {}{}",
        ev.chain_index,
        ev.height,
        short_id(&ev.receipt_hash),
        if ev.kinds.is_empty() {
            "—".to_string()
        } else {
            ev.kinds.join(", ")
        },
        ev.finality,
        if ev.has_proof { " · proof" } else { "" },
    )
}

/// The RECEIPTS face — the attached vat's chronicle tail (snapshot-seeded,
/// stream-advanced), newest last. The un-lie-able record: every row is a
/// receipt the vat's executor committed; the verify-against-your-own-anchor
/// affordance is the named next increment on exactly these hashes.
pub fn render_receipts_face(link: Option<&VatLink>, scroll: &ScrollHandle) -> AnyElement {
    let mut col = div()
        .id("dregg-computers-receipts")
        .bg(gpui::rgb(0x101820))
        .text_color(gpui::rgb(0x9fe0a0))
        .p_2()
        .flex()
        .flex_col()
        .gap_1();

    let Some(link) = link else {
        col = col
            .child(
                div()
                    .text_color(gpui::rgb(0x6fc0ff))
                    .child("── Receipt stream "),
            )
            .child(div().child("(not attached — nothing to witness yet)"));
        return nt_scroll_face(scroll, col).into_any_element();
    };

    let receipts = link.feed.receipts();
    let n = receipts.len();
    col = col.child(div().text_color(gpui::rgb(0x6fc0ff)).child(format!(
        "── Receipt stream · {n} received · {} · cursor {} ",
        if link.streaming() {
            "live SSE"
        } else {
            "snapshot only (no live socket)"
        },
        link.feed
            .resume_cursor()
            .map(|c| c.to_string())
            .unwrap_or_else(|| "—".to_string()),
    )));
    if n == 0 {
        return nt_scroll_face(
            scroll,
            col.child(div().child("(no receipts yet — the computer is quiet)")),
        )
        .into_any_element();
    }
    // The last ~24 receipts, newest last (the dense scrolling log discipline).
    let start = n.saturating_sub(24);
    for ev in receipts.iter().skip(start) {
        col = col.child(div().text_size(px(11.0)).child(receipt_row_text(ev)));
    }
    nt_scroll_face(scroll, col).into_any_element()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The tab vocabulary is stable and its labels are the ones the strip draws.
    #[test]
    fn the_faces_are_computers_connection_receipts() {
        assert_eq!(DreggComputersTab::ALL.len(), 3);
        assert_eq!(DreggComputersTab::default(), DreggComputersTab::Computers);
        assert_eq!(DreggComputersTab::Connection.label(), "Connection");
        assert_eq!(DreggComputersTab::Receipts.label(), "Receipts");
    }

    /// The fixture roster names itself a FIXTURE (and points at the live seam),
    /// carries the three honest lifecycle postures, and picks the mock backend
    /// for a connect — no network is ever attempted off the fixture.
    #[test]
    fn fixture_roster_is_honest_about_itself() {
        let dir = VatDirectory::fixture();
        assert_eq!(dir.source, DirectorySource::Fixture);
        assert!(dir.error.is_none());
        assert_eq!(dir.vats.len(), 3);
        assert!(dir.describe().contains("FIXTURE"));
        assert!(
            dir.describe().contains(crate::client::VATS_ROUTE),
            "the live seam is NAMED on the glass: {}",
            dir.describe()
        );

        // Running vat: reachable; sleeping vat: committed root, no endpoint;
        // unfunded vat: nothing launched.
        let running = dir.vat(&"dc".repeat(32)).expect("mybox on the roster");
        assert_eq!(running.state, "running");
        assert!(running.endpoint.is_some());
        let sleeping = dir.vat(&"5e".repeat(32)).expect("nightshift on the roster");
        assert!(sleeping.endpoint.is_none());
        assert!(sleeping.checkpoint_root.is_some());
        let unfunded = dir.vat(&"7a".repeat(32)).expect("scratch on the roster");
        assert!(!unfunded.funded);

        // A fixture connect rides the mock backend — real shapes, no socket.
        let client = dir.client_for(running).expect("fixture vats connect");
        assert!(!client.is_live());
    }

    /// A gateway-sourced vat with no endpoint REFUSES the connect honestly
    /// (nothing is listening) instead of attaching a mock that would lie.
    #[test]
    fn gateway_vat_without_endpoint_refuses_connect() {
        let dir = VatDirectory {
            vats: crate::client::mock::vats(),
            source: DirectorySource::Gateway("http://gateway.example".into()),
            error: None,
        };
        let sleeping = dir.vat(&"5e".repeat(32)).unwrap();
        // (`.err()` rather than `expect_err` — `NodeClient` carries no `Debug`.)
        let err = dir
            .client_for(sleeping)
            .err()
            .expect("no endpoint, no attach");
        assert!(err.contains("no reachable endpoint"), "{err}");
        // The running one connects at its REAL endpoint over HTTP.
        let running = dir.vat(&"dc".repeat(32)).unwrap();
        let client = dir.client_for(running).unwrap();
        assert!(client.is_live());
        assert_eq!(client.describe(), "http://127.0.0.1:8730");
    }

    /// Attaching a fixture vat over the mock backend reflects the full remote
    /// picture — status, cells, and a receipt tail — through the SAME wire
    /// model a live endpoint feeds, and pump() is a quiet no-op without a
    /// socket (the snapshot never pretends to stream).
    #[test]
    fn mock_attach_reflects_status_cells_and_receipts() {
        let dir = VatDirectory::fixture();
        let vat = dir.vat(&"dc".repeat(32)).unwrap().clone();
        let client = dir.client_for(&vat).unwrap();
        let mut link = VatLink::connect_with(vat, client);

        assert!(link.error.is_none());
        assert!(link.status.as_ref().is_some_and(|s| s.healthy));
        assert_eq!(link.cells.len(), 3, "the remote census reflected");
        assert_eq!(link.feed.receipts().len(), 2, "the snapshot receipt tail");
        assert_eq!(link.feed.resume_cursor(), Some(142));
        assert!(!link.streaming(), "no socket on the mock — named honestly");
        assert_eq!(link.pump(), 0);
        assert!(link.describe().contains("snapshot"));

        // The row twin carries the receipt's chain index + hash + finality —
        // the text a bake asserts against.
        let row = receipt_row_text(&link.feed.receipts()[1]);
        assert!(row.contains("#142"), "{row}");
        assert!(row.contains("committed"), "{row}");
    }

    /// The card text twin carries every rental truth the card paints — name,
    /// lifecycle, funding, settle count, witness mode, whereabouts, cap scope.
    #[test]
    fn vat_card_text_carries_the_rental_truths() {
        let vats = crate::client::mock::vats();
        let running = vat_card_text(&vats[0]);
        assert!(running.contains("mybox"));
        assert!(running.contains("running"));
        assert!(running.contains("funded"));
        assert!(running.contains("endpoint http://127.0.0.1:8730"));
        assert!(running.contains("vat:"), "the capability scope is named");

        let sleeping = vat_card_text(&vats[1]);
        assert!(sleeping.contains("sleeping"));
        assert!(
            sleeping.contains("checkpoint"),
            "asleep = its committed root"
        );
        assert!(sleeping.contains("symbolic"));

        let unfunded = vat_card_text(&vats[2]);
        assert!(unfunded.contains("UNFUNDED"));
        assert_eq!(vat_state_color("running"), NT_OK);
        assert_eq!(vat_state_color("sleeping"), NT_WARN);
        assert_eq!(vat_state_color("created"), NT_DIM);
    }
}
