//! `node.subscribe(filter)` — the SDK edge of the receipt nervous system.
//!
//! REFINEMENT-DESIGN.md Decision 3: the node broadcasts every committed
//! receipt at `GET /api/events/stream` (SSE). [`NodeEvents::subscribe`]
//! turns that into a reconnecting `Stream` of the public [`Receipt`] noun —
//! the same artifact `.turn()….sign()?.submit()?` returns, so observation
//! and action speak one language.
//!
//! Delivery: exactly-once per connection (the node streams its receipt
//! chain by cursor), at-least-once across reconnects (`Last-Event-ID`
//! resume; a receipt interrupted mid-delivery may repeat — dedupe by
//! `receipt_hash()` if it matters). Receipts arrive proofless when the
//! STARK is still in the node's async prove pool; fetch the attestation
//! later via `/api/receipts/{hash}/witnesses`.
//!
//! ```no_run
//! # async fn demo() -> Result<(), dregg_sdk::SdkError> {
//! use dregg_sdk_net::events::{NodeEvents, ReceiptFilter};
//!
//! let node = NodeEvents::new("http://localhost:8421");
//! let mut receipts = node.subscribe(ReceiptFilter::default());
//! while let Some(receipt) = receipts.next().await {
//!     println!("committed: {}", dregg_types::hex_encode(&receipt.turn_hash));
//! }
//! # Ok(()) }
//! ```

use std::pin::Pin;
use std::task::{Context, Poll};
use std::time::Duration;

use dregg_cell::CellId;
use dregg_turn::TurnReceipt;
use serde::Deserialize;
use tokio::sync::mpsc;

use dregg_sdk::receipt::Receipt;

/// Server-side stream filter (`?cell=…&kind=…`).
#[derive(Clone, Debug, Default)]
pub struct ReceiptFilter {
    cell: Option<String>,
    kind: Option<String>,
}

impl ReceiptFilter {
    /// Only receipts touching `cell` (the agent cell, an event-emitting
    /// cell, or the commit record's cell).
    pub fn cell(mut self, cell: CellId) -> Self {
        self.cell = Some(dregg_types::hex_encode(&cell.0));
        self
    }

    /// [`Self::cell`] with a raw hex id (e.g. straight from an explorer URL).
    pub fn cell_hex(mut self, cell: impl Into<String>) -> Self {
        self.cell = Some(cell.into());
        self
    }

    /// Only receipts whose commit record names this effect kind
    /// (e.g. `set_field`, `transfer`, `turn_committed`).
    pub fn kind(mut self, kind: impl Into<String>) -> Self {
        self.kind = Some(kind.into());
        self
    }

    fn query(&self) -> Vec<(&'static str, String)> {
        let mut q = Vec::new();
        if let Some(c) = &self.cell {
            q.push(("cell", c.clone()));
        }
        if let Some(k) = &self.kind {
            q.push(("kind", k.clone()));
        }
        q
    }
}

/// A node's event surface: subscribe to its committed-receipt stream.
#[derive(Clone, Debug)]
pub struct NodeEvents {
    base_url: String,
    client: reqwest::Client,
}

impl NodeEvents {
    /// Point at a node's base URL (e.g. `http://localhost:8421`).
    pub fn new(base_url: impl Into<String>) -> Self {
        NodeEvents {
            base_url: base_url.into().trim_end_matches('/').to_string(),
            client: reqwest::Client::new(),
        }
    }

    /// Subscribe to the node's committed receipts. Reconnects with
    /// exponential backoff and `Last-Event-ID` resume; the stream ends only
    /// when dropped. Must be called within a tokio runtime.
    pub fn subscribe(&self, filter: ReceiptFilter) -> ReceiptStream {
        let (tx, rx) = mpsc::channel(64);
        let client = self.client.clone();
        let url = format!("{}/api/events/stream", self.base_url);
        let task = tokio::spawn(run_subscription(client, url, filter, tx));
        ReceiptStream { rx, task }
    }
}

/// The wire envelope of one SSE `receipt` event (summary fields are served
/// for curl consumers; the SDK only needs the canonical receipt).
#[derive(Deserialize)]
struct WireReceiptEvent {
    receipt: TurnReceipt,
    #[serde(default)]
    proof_status: Option<String>,
}

async fn run_subscription(
    client: reqwest::Client,
    url: String,
    filter: ReceiptFilter,
    tx: mpsc::Sender<Receipt>,
) {
    let mut last_event_id: Option<String> = None;
    let mut backoff = Duration::from_millis(500);
    loop {
        let mut req = client
            .get(&url)
            .query(&filter.query())
            .header("accept", "text/event-stream");
        if let Some(id) = &last_event_id {
            req = req.header("last-event-id", id.clone());
        }
        match req.send().await {
            Ok(mut resp) if resp.status().is_success() => {
                let mut parser = SseParser::default();
                while let Ok(Some(chunk)) = resp.chunk().await {
                    for event in parser.push(&chunk) {
                        if let Some(id) = &event.id {
                            last_event_id = Some(id.clone());
                        }
                        if event.name.as_deref() != Some("receipt") {
                            continue;
                        }
                        let Ok(wire) = serde_json::from_str::<WireReceiptEvent>(&event.data) else {
                            continue;
                        };
                        if tx
                            .send(
                                Receipt::new(wire.receipt)
                                    .with_proof_status_hint(wire.proof_status),
                            )
                            .await
                            .is_err()
                        {
                            return; // consumer dropped the stream
                        }
                        backoff = Duration::from_millis(500);
                    }
                    if tx.is_closed() {
                        return;
                    }
                }
            }
            _ => {}
        }
        if tx.is_closed() {
            return;
        }
        tokio::time::sleep(backoff).await;
        backoff = (backoff * 2).min(Duration::from_secs(15));
    }
}

#[derive(Default)]
struct SseEvent {
    id: Option<String>,
    name: Option<String>,
    data: String,
}

/// Minimal SSE parser: splits the byte stream into events on blank lines,
/// honoring `id:` / `event:` / `data:` fields and ignoring `:` comments
/// (the node's 30s heartbeat).
#[derive(Default)]
struct SseParser {
    buf: String,
    current: SseEvent,
}

impl SseParser {
    fn push(&mut self, chunk: &[u8]) -> Vec<SseEvent> {
        self.buf.push_str(&String::from_utf8_lossy(chunk));
        let mut done = Vec::new();
        while let Some(nl) = self.buf.find('\n') {
            let line: String = self.buf.drain(..=nl).collect();
            let line = line.trim_end_matches(['\n', '\r']);
            if line.is_empty() {
                let event = std::mem::take(&mut self.current);
                if !event.data.is_empty() {
                    done.push(event);
                }
                continue;
            }
            if line.starts_with(':') {
                continue; // heartbeat / comment
            }
            let (field, value) = match line.split_once(':') {
                Some((f, v)) => (f, v.strip_prefix(' ').unwrap_or(v)),
                None => (line, ""),
            };
            match field {
                "id" => self.current.id = Some(value.to_string()),
                "event" => self.current.name = Some(value.to_string()),
                "data" => {
                    if !self.current.data.is_empty() {
                        self.current.data.push('\n');
                    }
                    self.current.data.push_str(value);
                }
                _ => {}
            }
        }
        done
    }
}

/// The live receipt feed: a `Stream<Item = Receipt>` (also consumable
/// without `StreamExt` via the inherent [`next`](Self::next)). Dropping it
/// ends the subscription.
#[derive(Debug)]
pub struct ReceiptStream {
    rx: mpsc::Receiver<Receipt>,
    task: tokio::task::JoinHandle<()>,
}

impl ReceiptStream {
    /// The next committed receipt (`None` only if the subscription task
    /// died — it otherwise reconnects forever).
    pub async fn next(&mut self) -> Option<Receipt> {
        self.rx.recv().await
    }
}

impl futures_core::Stream for ReceiptStream {
    type Item = Receipt;

    fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        self.get_mut().rx.poll_recv(cx)
    }
}

impl Drop for ReceiptStream {
    fn drop(&mut self) {
        self.task.abort();
    }
}
