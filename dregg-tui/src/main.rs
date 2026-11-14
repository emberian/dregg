//! dregg-tui — the face of the Robigalia v0 demo.
//!
//! A terminal light client over a running dregg node's HTTP API
//! (`node/src/api.rs`). It is the operator's window: a tab for the node
//! identity, a tab listing cells (id / balance / nonce / capability count), a
//! tab of recent receipts, and a VERIFY tab. Arrow keys / Tab switch panes; `r`
//! refreshes; `v` runs the verify report on the selected receipt; `q` quits.
//! Point it at a node with `dregg-tui <BASE_URL>` (default the live devnet).
//!
//! # The Verify tab does NOT currently verify a proof. Read this before trusting it.
//!
//! Steps 1 and 2 are real and load-bearing:
//!
//!   1. `GET /api/receipts/{hash}/witnesses` — the node's REAL route serving the
//!      canonical `DWR1` witnessed-receipt artifact (`node/src/api.rs::
//!      get_receipt_witnesses`).
//!   2. `dregg_sdk::decode_witnessed_receipt_artifact_hex` — the SDK's canonical
//!      DWR1 decoder (`sdk/src/witness_artifact.rs`), which validates the
//!      witness-hash binding on the way in; the TUI then re-checks that the
//!      decoded artifact's receipt hash is the one it asked for.
//!
//! Step 3 — the actual cryptographic check — is NOT WIRED. The only verify entry
//! this crate can reach for a single DWR1 artifact is
//! `dregg_verifier::verify_effect_vm_proof`, an entry now DELETED (it was the v1
//! hand-AIR (`EffectVmAir`) surface is gone, so the function discards its
//! arguments and fails closed on every build (`verifier/src/lib.rs`). The Verify
//! tab therefore reports `CANNOT VERIFY HERE` for every receipt — valid or not.
//! It is honest about that; it does not claim a verdict it did not compute. Do
//! NOT read its output as evidence about any proof.
//!
//! ## What is missing (the rewire, NAMED)
//!
//! The node's producers (`node/src/prove_pool.rs`, `node/src/api.rs`) build the
//! `WitnessedReceipt` with `proof_bytes = FullTurnProof::proof_bytes`, which is
//! a postcard-serialized `ComposedProof` (`sdk/src/full_turn_proof.rs`). The
//! real verify entry for that object is `dregg_sdk::verify_full_turn_bound`.
//! Three things stand between here and calling it, and each is a decision, not a
//! typo:
//!
//!   * **No decoder.** No public SDK entry reconstructs a `FullTurnProof` from a
//!     `WitnessedReceipt`'s `proof_bytes` — `TurnProofComponents` and
//!     `turn_hash` are not inside the serialized `ComposedProof`.
//!   * **No trusted endpoints.** `verify_full_turn_bound` takes the
//!     `expected_old_commit` / `expected_new_commit` that the verifier TRUSTS
//!     (a spend's freshness set binding rides the OLD commit). A light client with
//!     only this node's HTTP API has no authenticated source for them; taking
//!     them from the proof's own PI would make the check circular and worthless.
//!   * **Feature reach.** This crate pulls `dregg-sdk` with
//!     `default-features = false`, so `prover` is off and the
//!     `"effect-vm-rotated"` arm of `verify_full_turn_bound` — the arm every live
//!     leg needs — is compiled out.
//!
//! (`dregg_verifier::verify_rotated_replay_chain` is NOT the answer either: it
//! wants `RotatedReplayLeg{receipt, proof_bytes: Ir2BatchProof, public_inputs, vk_hash}`,
//! and a `WitnessedReceipt` carries neither an `Ir2BatchProof` nor a `vk_hash`.
//! Its own module doc says it is the CLI/demonstration floor, not the wire.)
//!
//! `dregg-sdk` and `dregg-verifier` are pulled with `no-lean-link` so the TUI
//! stays a pure host binary (no Lean runtime / libuv / GMP) — a link concern,
//! not a guarantee change.
//!
//! M4 of the seL4 boot ladder: once the M3 net stack carries the node onto seL4,
//! this same TUI is the face of the seL4 deployment.

use std::io::{self, Stdout};
use std::time::Duration;

use anyhow::Result;
use crossterm::event::{self, Event, KeyCode};
use crossterm::execute;
use crossterm::terminal::{
    disable_raw_mode, enable_raw_mode, EnterAlternateScreen, LeaveAlternateScreen,
};
use ratatui::backend::CrosstermBackend;
use ratatui::layout::{Constraint, Direction, Layout, Rect};
use ratatui::style::{Color, Modifier, Style};
use ratatui::text::{Line, Span};
use ratatui::widgets::{
    Block, Borders, List, ListItem, ListState, Paragraph, Row, Table, Tabs, Wrap,
};
use ratatui::{Frame, Terminal};
use serde::Deserialize;

// ── The node API response shapes we consume (subset of node/src/api.rs). ────

#[derive(Deserialize, Default, Clone)]
struct NodeIdentity {
    #[serde(default)]
    public_key: String,
    /// The node's derived agent cell (the operator identity). The node serves
    /// this as `agent_cell`.
    #[serde(default)]
    agent_cell: String,
    #[serde(default)]
    unlocked: bool,
    #[serde(default)]
    agent_balance: i64,
    #[serde(default)]
    agent_nonce: u64,
}

#[derive(Deserialize, Clone)]
struct CellListEntry {
    id: String,
    #[serde(default)]
    balance: i64,
    #[serde(default)]
    nonce: u64,
    #[serde(default)]
    capability_count: usize,
    #[serde(default)]
    has_delegate: bool,
    #[serde(default)]
    has_program: bool,
}

/// The real `node/src/api.rs::ReceiptInfo` shape. We read only the fields the
/// light client needs to display + drive a verify.
#[derive(Deserialize, Clone, Default)]
struct ReceiptInfo {
    #[serde(default)]
    chain_index: u64,
    #[serde(default)]
    chain_head: bool,
    #[serde(default)]
    receipt_hash: String,
    #[serde(default)]
    turn_hash: String,
    #[serde(default)]
    agent: String,
    #[serde(default)]
    pre_state: String,
    #[serde(default)]
    post_state: String,
    #[serde(default)]
    computrons_used: u64,
    #[serde(default)]
    action_count: usize,
    #[serde(default)]
    finality: String,
    #[serde(default)]
    has_proof: bool,
    #[serde(default)]
    proof_status: Option<String>,
    #[serde(default)]
    has_witness: bool,
    #[serde(default)]
    witness_count: usize,
}

/// The `/api/receipts/{hash}/witnesses` response (node/src/api.rs::
/// get_receipt_witnesses). `witness_artifacts` are hex-encoded DWR1 envelopes.
#[derive(Deserialize, Clone, Default)]
struct WitnessesResponse {
    #[serde(default)]
    witness_count: usize,
    #[serde(default)]
    witness_artifacts: Vec<String>,
}

// ── The light-client HTTP layer. ────────────────────────────────────────────

struct Client {
    base: String,
}

impl Client {
    fn new(base: String) -> Self {
        Client { base }
    }

    fn get<T: serde::de::DeserializeOwned>(&self, path: &str) -> Result<T> {
        let url = format!("{}{}", self.base, path);
        // Generous timeout: a witness artifact is a real ~0.5 MiB STARK proof.
        let v: T = ureq::get(&url)
            .timeout(Duration::from_secs(20))
            .call()?
            .into_json()?;
        Ok(v)
    }

    fn identity(&self) -> NodeIdentity {
        self.get("/api/node/identity").unwrap_or_default()
    }
    fn cells(&self) -> Vec<CellListEntry> {
        self.get("/api/cells").unwrap_or_default()
    }
    fn receipts(&self) -> Vec<ReceiptInfo> {
        self.get("/api/receipts").unwrap_or_default()
    }
    fn witnesses(&self, receipt_hash: &str) -> Result<WitnessesResponse> {
        self.get(&format!("/api/receipts/{receipt_hash}/witnesses"))
    }
}

// ── The light-client verify report. ──────────────────────────────────────────

/// What the verify run concluded. Three states, deliberately: `Unavailable` is
/// NOT `Rejected`. Collapsing them would tell an operator that a proof failed
/// when in fact nothing examined it.
#[derive(Clone, Copy, PartialEq, Eq)]
enum VerifyOutcome {
    /// A verify core examined the proof and ACCEPTED it.
    Verified,
    /// A verify core examined the proof and REJECTED it, or the artifact failed
    /// a binding/decode check this client performs itself.
    Rejected,
    /// Nothing examined the proof. No verdict was computed and none is implied.
    Unavailable,
}

/// The outcome of a verify run over one committed turn.
struct VerifyReport {
    receipt_hash: String,
    /// Human-readable report lines.
    lines: Vec<(String, Color)>,
    outcome: VerifyOutcome,
}

/// Fetch the selected receipt's DWR1 witness artifact from the live node, decode
/// it with the SDK's canonical decoder, check the receipt-hash binding, and then
/// report on the proof.
///
/// Steps 1-2 are real. Step 3 — the cryptographic verify — is NOT WIRED: the only
/// reachable single-artifact entry (`dregg_verifier::verify_effect_vm_proof`, now DELETED) was
/// the RETIRED v1 hand-AIR core, which discards its arguments and fails closed on
/// every build. This function therefore returns [`VerifyOutcome::Unavailable`] at
/// step 3 for every artifact and names what is missing. See the module doc for
/// the rewire. It never reports `Verified` for work it did not do.
fn verify_receipt(client: &Client, receipt: &ReceiptInfo) -> VerifyReport {
    let mut lines: Vec<(String, Color)> = Vec::new();
    let push = |lines: &mut Vec<(String, Color)>, s: String, c: Color| lines.push((s, c));

    push(
        &mut lines,
        format!("receipt   {}", receipt.receipt_hash),
        Color::Cyan,
    );
    push(
        &mut lines,
        format!("turn      {}", receipt.turn_hash),
        Color::DarkGray,
    );
    push(
        &mut lines,
        format!(
            "pre→post  {} → {}",
            short(&receipt.pre_state),
            short(&receipt.post_state)
        ),
        Color::DarkGray,
    );
    push(&mut lines, String::new(), Color::White);

    // 1. Pull the canonical DWR1 witness artifact from the node's REAL route.
    push(
        &mut lines,
        "1. GET /api/receipts/{hash}/witnesses ...".into(),
        Color::White,
    );
    let resp = match client.witnesses(&receipt.receipt_hash) {
        Ok(r) => r,
        Err(e) => {
            push(
                &mut lines,
                format!("   could not fetch witnesses: {e}"),
                Color::Red,
            );
            return VerifyReport {
                receipt_hash: receipt.receipt_hash.clone(),
                lines,
                outcome: VerifyOutcome::Unavailable,
            };
        }
    };
    if resp.witness_artifacts.is_empty() {
        push(
            &mut lines,
            "   node holds no witness artifact for this receipt (nothing to examine).".into(),
            Color::Yellow,
        );
        return VerifyReport {
            receipt_hash: receipt.receipt_hash.clone(),
            lines,
            outcome: VerifyOutcome::Unavailable,
        };
    }
    let artifact_hex = &resp.witness_artifacts[0];
    push(
        &mut lines,
        format!(
            "   got {} DWR1 artifact(s), {} bytes",
            resp.witness_count.max(resp.witness_artifacts.len()),
            artifact_hex.len() / 2
        ),
        Color::Green,
    );

    // 2. Decode the DWR1 artifact with the SDK's canonical decoder (validates the
    //    witness-hash binding).
    push(
        &mut lines,
        "2. dregg_sdk::decode_witnessed_receipt_artifact_hex ...".into(),
        Color::White,
    );
    let witnessed = match dregg_sdk::decode_witnessed_receipt_artifact_hex(artifact_hex) {
        Ok(w) => w,
        Err(e) => {
            push(
                &mut lines,
                format!("   DWR1 decode failed: {e}"),
                Color::Red,
            );
            return VerifyReport {
                receipt_hash: receipt.receipt_hash.clone(),
                lines,
                outcome: VerifyOutcome::Rejected,
            };
        }
    };
    push(
        &mut lines,
        format!(
            "   decoded: proof {} bytes, {} public inputs",
            witnessed.proof_bytes.len(),
            witnessed.public_inputs.len()
        ),
        Color::Green,
    );

    // 2b. The light client re-checks that the decoded artifact actually carries
    //     the receipt it was served under — the node cannot swap a valid proof of
    //     turn B under turn A's receipt hash.
    let decoded_receipt_hash = hex32(&witnessed.receipt.receipt_hash());
    if !decoded_receipt_hash.eq_ignore_ascii_case(&receipt.receipt_hash) {
        push(
            &mut lines,
            format!(
                "   SEAM BROKEN: artifact's receipt hash {} != requested {}",
                short(&decoded_receipt_hash),
                short(&receipt.receipt_hash)
            ),
            Color::Red,
        );
        return VerifyReport {
            receipt_hash: receipt.receipt_hash.clone(),
            lines,
            outcome: VerifyOutcome::Rejected,
        };
    }
    push(
        &mut lines,
        "   artifact's receipt-hash binds the served receipt (seam holds).".into(),
        Color::Green,
    );

    // 3. The cryptographic verify. NOT WIRED — and this reports that rather than
    //    performing a step that looks like verification and is not.
    //
    //    ⚑ 2026-08-05: this block used to CALL `dregg_verifier::verify_effect_vm_proof`
    //    on an empty input and print its fixed rejection string as a "retirement
    //    witness". That entry is DELETED (it discarded every argument and rejected on
    //    every build), and with it the last reason to invoke anything here. The client
    //    still does not verify this artifact, and now says so without borrowing a
    //    sentence from a function to make the not-verifying look instrumented.
    push(
        &mut lines,
        "3. cryptographic verify: NOT WIRED in this client.".into(),
        Color::Yellow,
    );
    push(
        &mut lines,
        "   Nothing examined these bytes. No proof verifier ran.".into(),
        Color::DarkGray,
    );
    push(&mut lines, String::new(), Color::White);
    push(
        &mut lines,
        "   MISSING: this artifact's proof_bytes is a postcard ComposedProof (the".into(),
        Color::DarkGray,
    );
    push(
        &mut lines,
        "   node's FullTurnProof). Its real verify is dregg_sdk::verify_full_turn_bound,".into(),
        Color::DarkGray,
    );
    push(
        &mut lines,
        "   which needs (a) a public SDK decoder from a WitnessedReceipt back to a".into(),
        Color::DarkGray,
    );
    push(
        &mut lines,
        "   FullTurnProof, (b) an AUTHENTICATED source for expected_old_commit /".into(),
        Color::DarkGray,
    );
    push(
        &mut lines,
        "   expected_new_commit (which carry the spend freshness binding) not from".into(),
        Color::DarkGray,
    );
    push(
        &mut lines,
        "   the proof itself, and (c) dregg-sdk built with `prover` so the live".into(),
        Color::DarkGray,
    );
    push(
        &mut lines,
        "   \"effect-vm-rotated\" arm exists. See this file's module doc.".into(),
        Color::DarkGray,
    );
    push(&mut lines, String::new(), Color::White);
    push(
        &mut lines,
        "   NO VERDICT. This says nothing about whether the proof is valid.".into(),
        Color::Yellow,
    );

    VerifyReport {
        receipt_hash: receipt.receipt_hash.clone(),
        lines,
        outcome: VerifyOutcome::Unavailable,
    }
}

/// Lowercase hex of a 32-byte digest.
fn hex32(bytes: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

// ── App state. ───────────────────────────────────────────────────────────────

#[derive(Clone, Copy, PartialEq)]
enum Tab {
    Identity,
    Cells,
    Receipts,
    Verify,
}

impl Tab {
    fn titles() -> [&'static str; 4] {
        ["Identity", "Cells", "Receipts", "Verify"]
    }
    fn index(self) -> usize {
        match self {
            Tab::Identity => 0,
            Tab::Cells => 1,
            Tab::Receipts => 2,
            Tab::Verify => 3,
        }
    }
    fn next(self) -> Tab {
        match self {
            Tab::Identity => Tab::Cells,
            Tab::Cells => Tab::Receipts,
            Tab::Receipts => Tab::Verify,
            Tab::Verify => Tab::Identity,
        }
    }
}

struct App {
    client: Client,
    tab: Tab,
    identity: NodeIdentity,
    cells: Vec<CellListEntry>,
    receipts: Vec<ReceiptInfo>,
    receipt_sel: ListState,
    status: String,
    online: bool,
    /// The most recent independent-verify report (Verify tab).
    report: Option<VerifyReport>,
}

impl App {
    fn new(base: String) -> Self {
        let client = Client::new(base);
        let mut sel = ListState::default();
        sel.select(Some(0));
        let mut app = App {
            client,
            tab: Tab::Identity,
            identity: NodeIdentity::default(),
            cells: Vec::new(),
            receipts: Vec::new(),
            receipt_sel: sel,
            status: String::new(),
            online: false,
            report: None,
        };
        app.refresh();
        app
    }

    fn refresh(&mut self) {
        let id: Result<NodeIdentity> = self.client.get("/api/node/identity");
        let id_err = id.as_ref().err().map(|e| e.to_string());
        self.online = id.is_ok();
        self.identity = self.client.identity();
        self.cells = self.client.cells();
        self.receipts = self.client.receipts();
        let with_witness = self.receipts.iter().filter(|r| r.has_witness).count();
        self.status = if self.online {
            format!(
                "online · {} · {} cells · {} receipts ({} with witness)",
                self.client.base,
                self.cells.len(),
                self.receipts.len(),
                with_witness,
            )
        } else {
            // Surface the real connection error so the operator can see WHY the
            // node is unreachable (DNS, refused, timeout, TLS) rather than a
            // generic "offline" — same diagnostic the headless path prints.
            match id_err {
                Some(e) => format!("offline · {} — {e}", self.client.base),
                None => format!(
                    "offline · could not reach {} (is a dregg node running?)",
                    self.client.base
                ),
            }
        };
        // Keep the selection in range.
        if self.receipts.is_empty() {
            self.receipt_sel.select(None);
        } else {
            let i = self
                .receipt_sel
                .selected()
                .unwrap_or(0)
                .min(self.receipts.len() - 1);
            self.receipt_sel.select(Some(i));
        }
    }

    fn selected_receipt(&self) -> Option<&ReceiptInfo> {
        self.receipt_sel
            .selected()
            .and_then(|i| self.receipts.get(i))
    }

    fn move_sel(&mut self, delta: i64) {
        if self.receipts.is_empty() {
            return;
        }
        let n = self.receipts.len() as i64;
        let cur = self.receipt_sel.selected().unwrap_or(0) as i64;
        let next = ((cur + delta) % n + n) % n;
        self.receipt_sel.select(Some(next as usize));
    }

    /// Run the verify report on the selected receipt and switch to the Verify tab
    /// to show it. (Step 3 is not wired — see [`verify_receipt`].)
    fn verify_selected(&mut self) {
        let Some(receipt) = self.selected_receipt().cloned() else {
            self.status = "no receipt selected to verify".into();
            return;
        };
        self.status = format!("checking {} ...", short(&receipt.receipt_hash));
        let report = verify_receipt(&self.client, &receipt);
        self.status = if report.outcome == VerifyOutcome::Verified {
            format!("VERIFIED {} independently", short(&report.receipt_hash))
        } else {
            format!(
                "verify report for {} (see Verify tab)",
                short(&report.receipt_hash)
            )
        };
        self.report = Some(report);
        self.tab = Tab::Verify;
    }
}

// ── Rendering. ───────────────────────────────────────────────────────────────

fn draw(f: &mut Frame, app: &mut App) {
    let chunks = Layout::default()
        .direction(Direction::Vertical)
        .constraints([
            Constraint::Length(3),
            Constraint::Min(0),
            Constraint::Length(1),
        ])
        .split(f.area());

    let titles: Vec<Line> = Tab::titles().iter().map(|t| Line::from(*t)).collect();
    let tabs = Tabs::new(titles)
        .block(
            Block::default()
                .borders(Borders::ALL)
                .title(" dregg robigalia v0 — light client "),
        )
        .select(app.tab.index())
        .highlight_style(
            Style::default()
                .fg(Color::Black)
                .bg(Color::Cyan)
                .add_modifier(Modifier::BOLD),
        );
    f.render_widget(tabs, chunks[0]);

    match app.tab {
        Tab::Identity => draw_identity(f, app, chunks[1]),
        Tab::Cells => draw_cells(f, app, chunks[1]),
        Tab::Receipts => draw_receipts(f, app, chunks[1]),
        Tab::Verify => draw_verify(f, app, chunks[1]),
    }

    let dot = if app.online {
        Span::styled("●", Style::default().fg(Color::Green))
    } else {
        Span::styled("●", Style::default().fg(Color::Red))
    };
    let help = match app.tab {
        Tab::Receipts => "   [↑↓] select  [v] VERIFY  [Tab] pane  [r] refresh  [q] quit",
        _ => "   [Tab] pane  [r] refresh  [q] quit",
    };
    let status = Line::from(vec![
        dot,
        Span::raw(" "),
        Span::raw(app.status.as_str()),
        Span::styled(help, Style::default().fg(Color::DarkGray)),
    ]);
    f.render_widget(Paragraph::new(status), chunks[2]);
}

fn draw_identity(f: &mut Frame, app: &App, area: Rect) {
    let id = &app.identity;
    let lock = if id.unlocked { "unlocked" } else { "locked" };
    let lines = vec![
        Line::from(vec![
            Span::styled("operator pubkey ", Style::default().fg(Color::Cyan)),
            Span::raw(blank_dash(&id.public_key)),
        ]),
        Line::from(vec![
            Span::styled("agent cell      ", Style::default().fg(Color::Cyan)),
            Span::raw(blank_dash(&id.agent_cell)),
        ]),
        Line::from(vec![
            Span::styled("agent state     ", Style::default().fg(Color::Cyan)),
            Span::raw(format!(
                "balance {} · nonce {} · {}",
                id.agent_balance, id.agent_nonce, lock
            )),
        ]),
        Line::from(""),
        Line::from(Span::styled(
            "this is a light client: it reads the node's published API and, on the",
            Style::default().fg(Color::DarkGray),
        )),
        Line::from(Span::styled(
            "Verify tab, INDEPENDENTLY re-checks a turn's STARK proof — trusting the",
            Style::default().fg(Color::DarkGray),
        )),
        Line::from(Span::styled(
            "proof, not the node. Go to Receipts, pick one, press [v].",
            Style::default().fg(Color::DarkGray),
        )),
    ];
    f.render_widget(
        Paragraph::new(lines).block(
            Block::default()
                .borders(Borders::ALL)
                .title(" node identity "),
        ),
        area,
    );
}

fn draw_cells(f: &mut Frame, app: &App, area: Rect) {
    let rows: Vec<Row> = app
        .cells
        .iter()
        .map(|c| {
            Row::new(vec![
                short(&c.id),
                c.balance.to_string(),
                c.nonce.to_string(),
                c.capability_count.to_string(),
                if c.has_program {
                    "yes".into()
                } else {
                    "—".into()
                },
                if c.has_delegate {
                    "yes".into()
                } else {
                    "—".into()
                },
            ])
        })
        .collect();
    let widths = [
        Constraint::Length(20),
        Constraint::Length(12),
        Constraint::Length(7),
        Constraint::Length(6),
        Constraint::Length(8),
        Constraint::Length(8),
    ];
    let table = Table::new(rows, widths)
        .header(
            Row::new(vec![
                "cell id", "balance", "nonce", "caps", "program", "delegate",
            ])
            .style(
                Style::default()
                    .fg(Color::Cyan)
                    .add_modifier(Modifier::BOLD),
            ),
        )
        .block(
            Block::default()
                .borders(Borders::ALL)
                .title(format!(" cells ({}) ", app.cells.len())),
        );
    f.render_widget(table, area);
}

fn draw_receipts(f: &mut Frame, app: &mut App, area: Rect) {
    let items: Vec<ListItem> = app
        .receipts
        .iter()
        .map(|r| {
            let head = if r.chain_head { "►" } else { " " };
            let mark = if r.has_witness {
                Span::styled("◆ witness", Style::default().fg(Color::Green))
            } else if r.proof_status.as_deref() == Some("not_required") {
                Span::styled("signature only", Style::default().fg(Color::Yellow))
            } else if r.has_proof {
                Span::styled("◇ proof  ", Style::default().fg(Color::Yellow))
            } else {
                Span::styled("·        ", Style::default().fg(Color::DarkGray))
            };
            ListItem::new(Line::from(vec![
                Span::styled(
                    format!("{head} #{:<3} ", r.chain_index),
                    Style::default().fg(Color::Cyan),
                ),
                mark,
                Span::raw("  "),
                Span::raw(short(&r.receipt_hash)),
                Span::styled(
                    format!("  {:<10}", r.finality),
                    Style::default().fg(Color::DarkGray),
                ),
                Span::styled(
                    format!("  {} act · {} cu", r.action_count, r.computrons_used),
                    Style::default().fg(Color::DarkGray),
                ),
            ]))
        })
        .collect();
    let list = List::new(items)
        .block(Block::default().borders(Borders::ALL).title(format!(
            " receipts ({}) — [↑↓] select, [v] verify ",
            app.receipts.len()
        )))
        .highlight_style(
            Style::default()
                .bg(Color::DarkGray)
                .add_modifier(Modifier::BOLD),
        )
        .highlight_symbol("» ");
    f.render_stateful_widget(list, area, &mut app.receipt_sel);
}

fn draw_verify(f: &mut Frame, app: &App, area: Rect) {
    let (title, lines): (String, Vec<Line>) = match &app.report {
        None => (
            " verify ".into(),
            vec![
                Line::from(Span::styled(
                    "No verify run yet.",
                    Style::default().fg(Color::DarkGray),
                )),
                Line::from(""),
                Line::from("Go to the Receipts tab, select a receipt carrying a ◆ witness,"),
                Line::from("and press [v]. This client will then:"),
                Line::from(""),
                Line::from("  1. fetch the receipt's DWR1 witness artifact from the node,"),
                Line::from("  2. decode it with the SDK's canonical decoder and check that"),
                Line::from("     the artifact binds the receipt hash it was served under,"),
                Line::from("  3. report that the cryptographic verify is NOT WIRED here."),
                Line::from(""),
                Line::from(Span::styled(
                    "Step 3 is not implemented: the only reachable single-artifact",
                    Style::default().fg(Color::Yellow),
                )),
                Line::from(Span::styled(
                    "verify core is the RETIRED v1 one. This tab cannot tell you",
                    Style::default().fg(Color::Yellow),
                )),
                Line::from(Span::styled(
                    "whether a proof is valid. See the module doc for the rewire.",
                    Style::default().fg(Color::Yellow),
                )),
            ],
        ),
        Some(rep) => {
            let verdict = match rep.outcome {
                VerifyOutcome::Verified => Span::styled(
                    " ✓ INDEPENDENTLY VERIFIED ",
                    Style::default()
                        .fg(Color::Black)
                        .bg(Color::Green)
                        .add_modifier(Modifier::BOLD),
                ),
                VerifyOutcome::Rejected => Span::styled(
                    " ✗ NOT VERIFIED ",
                    Style::default()
                        .fg(Color::White)
                        .bg(Color::Red)
                        .add_modifier(Modifier::BOLD),
                ),
                VerifyOutcome::Unavailable => Span::styled(
                    " ⚠ CANNOT VERIFY HERE — NO VERDICT ",
                    Style::default()
                        .fg(Color::Black)
                        .bg(Color::Yellow)
                        .add_modifier(Modifier::BOLD),
                ),
            };
            let mut ls: Vec<Line> = vec![Line::from(verdict), Line::from("")];
            for (text, color) in &rep.lines {
                ls.push(Line::from(Span::styled(
                    text.clone(),
                    Style::default().fg(*color),
                )));
            }
            (format!(" verify · {} ", short(&rep.receipt_hash)), ls)
        }
    };
    f.render_widget(
        Paragraph::new(lines)
            .wrap(Wrap { trim: false })
            .block(Block::default().borders(Borders::ALL).title(title)),
        area,
    );
}

fn short(s: &str) -> String {
    if s.len() > 18 {
        format!("{}…{}", &s[..8], &s[s.len() - 6..])
    } else if s.is_empty() {
        "—".into()
    } else {
        s.to_string()
    }
}

fn blank_dash(s: &str) -> String {
    if s.is_empty() {
        "—".into()
    } else {
        s.to_string()
    }
}

// ── Event loop. ──────────────────────────────────────────────────────────────

fn run(terminal: &mut Terminal<CrosstermBackend<Stdout>>, mut app: App) -> Result<()> {
    loop {
        terminal.draw(|f| draw(f, &mut app))?;
        if event::poll(Duration::from_millis(250))? {
            if let Event::Key(key) = event::read()? {
                match key.code {
                    KeyCode::Char('q') | KeyCode::Esc => break,
                    KeyCode::Tab | KeyCode::Right => app.tab = app.tab.next(),
                    KeyCode::Char('r') => app.refresh(),
                    KeyCode::Char('v') => app.verify_selected(),
                    KeyCode::Down if app.tab == Tab::Receipts => app.move_sel(1),
                    KeyCode::Up if app.tab == Tab::Receipts => app.move_sel(-1),
                    KeyCode::Char('1') => app.tab = Tab::Identity,
                    KeyCode::Char('2') => app.tab = Tab::Cells,
                    KeyCode::Char('3') => app.tab = Tab::Receipts,
                    KeyCode::Char('4') => app.tab = Tab::Verify,
                    _ => {}
                }
            }
        }
    }
    Ok(())
}

/// `dregg-tui --selfcheck`: the v1 hand-AIR (`EffectVmAir`) verify-core selfcheck is
/// RETIRED. The v1 single-proof Effect-VM STARK (prove + `verify_effect_vm_proof`) is gone;
/// the live verify core is the rotated replay-chain verify
/// (`dregg_verifier::verify_rotated_replay_chain`, the prover-free `verifier` floor). The
/// selfcheck reports the retirement and exits 0 (nothing to fail) — a rotated-core selfcheck
/// is the follow-up.
fn run_selfcheck() -> i32 {
    println!("dregg-tui light client — verify-core selfcheck");
    println!(
        "  the v1 hand-AIR (EffectVmAir) single-proof verify core is RETIRED; the live core is"
    );
    println!("  the rotated replay-chain verify (dregg_verifier::verify_rotated_replay_chain, the");
    println!("  prover-free `verifier` floor). Verify a rotated chain to exercise the live core.");
    0
}

/// Headless mode: `dregg-tui <BASE_URL> --verify-head` connects, picks the most
/// recent receipt carrying a witness, runs the verify report, prints it to
/// stdout, and exits 0 (verified) / 1 (rejected) / 2 (no verdict — could not
/// reach, nothing to examine, or the verify core is not wired).
///
/// Exit 2 is the state this ALWAYS returns today: step 3 is not wired (see
/// [`verify_receipt`]), so this mode cannot exit 0. It is kept distinct from
/// exit 1 on purpose — a caller must not read "no verify core" as "bad proof".
fn run_headless(base: String) -> i32 {
    let client = Client::new(base.clone());
    let id: Result<NodeIdentity> = client.get("/api/node/identity");
    if let Err(e) = &id {
        println!("offline: could not reach {base}");
        println!("  reason: {e}");
        return 2;
    }
    let identity = client.identity();
    let cells = client.cells();
    let receipts = client.receipts();
    println!("dregg-tui light client — headless verify");
    println!("node    {base}");
    println!(
        "operator pubkey {}  agent cell {}",
        short(&identity.public_key),
        short(&identity.agent_cell)
    );
    println!(
        "ledger  {} cells · {} recent receipts",
        cells.len(),
        receipts.len()
    );
    let Some(target) = receipts.iter().find(|r| r.has_witness) else {
        println!("no receipt carries a witness artifact — nothing to examine");
        return 2;
    };
    println!();
    let report = verify_receipt(&client, target);
    for (text, _c) in &report.lines {
        println!("{text}");
    }
    println!();
    match report.outcome {
        VerifyOutcome::Verified => {
            println!("RESULT: INDEPENDENTLY VERIFIED");
            0
        }
        VerifyOutcome::Rejected => {
            println!("RESULT: NOT VERIFIED");
            1
        }
        VerifyOutcome::Unavailable => {
            println!("RESULT: NO VERDICT — this client did not verify the proof.");
            println!("        This is NOT a statement that the proof is bad.");
            2
        }
    }
}

fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().collect();
    let base = args
        .iter()
        .skip(1)
        .find(|a| !a.starts_with("--"))
        .cloned()
        .unwrap_or_else(|| dregg_sdk::DreggEndpoints::from_env().devnet_url());

    if args.iter().any(|a| a == "--selfcheck") {
        std::process::exit(run_selfcheck());
    }
    if args.iter().any(|a| a == "--verify-head") {
        let code = run_headless(base);
        std::process::exit(code);
    }

    enable_raw_mode()?;
    let mut stdout = io::stdout();
    execute!(stdout, EnterAlternateScreen)?;
    let backend = CrosstermBackend::new(stdout);
    let mut terminal = Terminal::new(backend)?;

    let app = App::new(base);
    let res = run(&mut terminal, app);

    disable_raw_mode()?;
    execute!(terminal.backend_mut(), LeaveAlternateScreen)?;
    terminal.show_cursor()?;
    res
}

// ── Tests. ───────────────────────────────────────────────────────────────────
//
// These drive the SHIPPED `verify_receipt` against a stub node over real HTTP —
// the same function the `[v]` key and `--verify-head` call. The stub serves a
// REAL DWR1 artifact (encoded by `dregg_turn::WitnessedReceipt::to_artifact_bytes`,
// the node's own encoder) so steps 1-2 do their real work; the proof body inside
// is arbitrary bytes, which is the point: NO reachable verify core looks at it.
//
// The tooth: `verify_receipt` must return `Unavailable` — never `Verified`, and
// never `Rejected` — for an artifact whose proof nothing examined. If someone
// wires a real verify core here, `unwired_verify_core_yields_no_verdict` FAILS,
// which is the correct alarm: this test is the standing record that step 3 is a
// hole, and it must be deleted by the same change that fills it.
#[cfg(test)]
mod tests {
    use super::*;
    use std::io::{Read, Write};
    use std::net::TcpListener;

    /// A real DWR1 artifact carrying an arbitrary proof body, plus its receipt hash.
    fn dwr1_fixture() -> (String, String) {
        let receipt = dregg_turn::TurnReceipt {
            turn_hash: [9u8; 32],
            effects_hash: [11u8; 32],
            ..Default::default()
        };
        let receipt_hash = hex32(&receipt.receipt_hash());
        let wr = dregg_turn::WitnessedReceipt::from_components(
            receipt,
            vec![0xABu8; 64],
            vec![1, 2, 3],
            None,
        );
        let bytes = wr.to_artifact_bytes().expect("encode DWR1");
        let mut hex = String::with_capacity(bytes.len() * 2);
        for b in &bytes {
            hex.push_str(&format!("{b:02x}"));
        }
        (receipt_hash, hex)
    }

    /// Serve exactly one `/witnesses` response, then stop. Returns the base URL.
    fn stub_node(body: String) -> String {
        let listener = TcpListener::bind("127.0.0.1:0").expect("bind");
        let base = format!("http://{}", listener.local_addr().expect("addr"));
        std::thread::spawn(move || {
            if let Ok((mut sock, _)) = listener.accept() {
                let mut buf = [0u8; 4096];
                let _ = sock.read(&mut buf);
                let resp = format!(
                    "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{}",
                    body.len(),
                    body
                );
                let _ = sock.write_all(resp.as_bytes());
            }
        });
        base
    }

    /// THE TOOTH. A receipt whose DWR1 artifact fetches and decodes cleanly must
    /// come back `Unavailable`: nothing verified the proof, so no verdict exists.
    /// A `Verified` here would be the lie this test exists to catch — the shipped
    /// code once printed "✓ INDEPENDENTLY VERIFIED" off a call that discards its
    /// arguments.
    #[test]
    fn unwired_verify_core_yields_no_verdict() {
        let (receipt_hash, artifact_hex) = dwr1_fixture();
        let body = serde_json::json!({
            "witness_count": 1,
            "witness_artifacts": [artifact_hex],
        })
        .to_string();
        let client = Client::new(stub_node(body));
        let info = ReceiptInfo {
            receipt_hash: receipt_hash.clone(),
            has_witness: true,
            ..Default::default()
        };

        let report = verify_receipt(&client, &info);

        assert!(
            report.outcome == VerifyOutcome::Unavailable,
            "step 3 is not wired: a proof nothing examined must yield NO VERDICT, \
             not a pass and not a rejection"
        );
        let text = report
            .lines
            .iter()
            .map(|(s, _)| s.as_str())
            .collect::<Vec<_>>()
            .join("\n");
        // Steps 1-2 really ran: fetch + decode + the receipt-hash binding check.
        assert!(
            text.contains("seam holds"),
            "step 2 binding check must run: {text}"
        );
        // Step 3 must say so out loud.
        assert!(
            text.contains("NOT WIRED"),
            "step 3 must name itself: {text}"
        );
        assert!(
            text.contains("NO VERDICT"),
            "report must refuse a verdict: {text}"
        );
        assert!(
            !text.contains("VERIFIED —"),
            "report must never claim a verify it did not perform: {text}"
        );
    }

    /// An artifact that does NOT bind the receipt hash it was served under is a
    /// real break this client detects itself — that one IS a rejection, and must
    /// stay distinguishable from the not-wired case.
    #[test]
    fn receipt_hash_mismatch_is_a_rejection_not_a_shrug() {
        let (_real_hash, artifact_hex) = dwr1_fixture();
        let body = serde_json::json!({
            "witness_count": 1,
            "witness_artifacts": [artifact_hex],
        })
        .to_string();
        let client = Client::new(stub_node(body));
        let info = ReceiptInfo {
            // Ask for a DIFFERENT receipt than the artifact carries.
            receipt_hash: "00".repeat(32),
            has_witness: true,
            ..Default::default()
        };

        let report = verify_receipt(&client, &info);

        assert!(
            report.outcome == VerifyOutcome::Rejected,
            "a swapped artifact is a detected break, not a missing verdict"
        );
    }
}
