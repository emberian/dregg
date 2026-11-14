//! `GET /api/events/stream` — the receipt nervous system (SSE).
//!
//! REFINEMENT-DESIGN.md Decision 3: cells are law, agents are will, receipts
//! are the nervous system. This is the nervous system's node edge: a
//! Server-Sent-Events broadcast of every receipt the node commits, taken
//! from the one tap that already exists — the [`NodeEvent`] broadcast that
//! every commit path (HTTP submit, signed-envelope ingress, MCP, blocklace
//! finalization) fires after appending to the cipherclerk receipt chain.
//!
//! Delivery model: the broadcast is only a WAKE-UP; the receipt chain itself
//! is the cursor's source of truth, so a lagged broadcast subscriber loses
//! nothing — the cursor re-reads the chain and catches up. Each event carries
//! `id: <chain_index>`; a reconnecting client sends `Last-Event-ID` and the
//! stream resumes from the next chain entry (exactly-once per connection,
//! at-least-once across reconnects). `has_proof` is the value at send time;
//! proofs attach asynchronously (re-check `/api/receipts/{hash}/witnesses`).
//! `proof_status: "not_required"` explicitly identifies coordination turns with
//! signature attestation only; these do not promise a future validity proof.
//!
//! Filtering: `?cell=<hex id>` (agent cell or any cell named by the
//! receipt's emitted events / commit record) and `?kind=<effect kind>`
//! (matched against the commit record's effect summaries).

use std::collections::HashMap;
use std::convert::Infallible;
use std::net::IpAddr;
use std::sync::{Arc, Mutex};
use std::time::Duration;

use axum::extract::{ConnectInfo, Query, State};
use axum::http::HeaderMap;
use axum::response::sse::{Event, KeepAlive, Sse};
use dregg_types::hex_encode;
use futures_util::stream::Stream;
use serde::{Deserialize, Serialize};
use tokio::sync::{OwnedSemaphorePermit, Semaphore, broadcast};

use crate::state::{NodeEvent, NodeState, NodeStateInner};

/// ANON-DoS #3 — the default cap on concurrently-open receipt-stream (SSE)
/// connections node-wide. Each live stream holds a `broadcast::Receiver` and
/// re-acquires `state.read()` on every drain, so an unbounded fan of streams is a
/// cheap way to pin the node's read path. A global [`Semaphore`] hard-caps the
/// total; a per-IP counter stops one peer from consuming the whole budget.
pub const MAX_LIVE_SSE_CONNECTIONS: usize = 512;
/// ANON-DoS #3 — the default per-IP cap on concurrent SSE connections.
pub const MAX_SSE_CONNECTIONS_PER_IP: u32 = 16;

/// Shared admission control for the receipt SSE stream (ANON-DoS #3): a global
/// permit pool plus a per-IP live-connection tally. Constructed once in the
/// router and cloned into the handler; each accepted stream holds a permit + a
/// per-IP slot for its whole lifetime (released on disconnect via RAII).
#[derive(Clone)]
pub struct SseLimits {
    sem: Arc<Semaphore>,
    per_ip: Arc<Mutex<HashMap<IpAddr, u32>>>,
    per_ip_max: u32,
}

impl SseLimits {
    pub fn new(global_max: usize, per_ip_max: u32) -> Self {
        Self {
            sem: Arc::new(Semaphore::new(global_max.max(1))),
            per_ip: Arc::new(Mutex::new(HashMap::new())),
            per_ip_max: per_ip_max.max(1),
        }
    }

    /// Default limits ([`MAX_LIVE_SSE_CONNECTIONS`] / [`MAX_SSE_CONNECTIONS_PER_IP`]).
    pub fn with_defaults() -> Self {
        Self::new(MAX_LIVE_SSE_CONNECTIONS, MAX_SSE_CONNECTIONS_PER_IP)
    }

    /// Try to admit a new stream from `ip`. Returns an [`SseSlot`] (holding the
    /// global permit + the per-IP reservation) on success, or `None` when the
    /// global pool is exhausted or this IP is already at its per-IP cap.
    fn try_admit(&self, ip: IpAddr) -> Option<SseSlot> {
        let permit = Arc::clone(&self.sem).try_acquire_owned().ok()?;
        {
            let mut map = self.per_ip.lock().expect("sse per-ip mutex");
            let slot = map.entry(ip).or_insert(0);
            if *slot >= self.per_ip_max {
                // Global permit `permit` drops here, returning it to the pool.
                return None;
            }
            *slot += 1;
        }
        Some(SseSlot {
            _permit: permit,
            per_ip: Arc::clone(&self.per_ip),
            ip,
        })
    }
}

/// RAII admission slot for one live SSE stream. Holding it keeps a global permit
/// reserved and one unit of this IP's per-IP tally; dropping it (on disconnect,
/// when the stream is dropped) releases both.
struct SseSlot {
    _permit: OwnedSemaphorePermit,
    per_ip: Arc<Mutex<HashMap<IpAddr, u32>>>,
    ip: IpAddr,
}

impl Drop for SseSlot {
    fn drop(&mut self) {
        if let Ok(mut map) = self.per_ip.lock() {
            if let Some(n) = map.get_mut(&self.ip) {
                *n = n.saturating_sub(1);
                if *n == 0 {
                    map.remove(&self.ip);
                }
            }
        }
        // `_permit` drops here, returning the global permit to the pool.
    }
}

/// Optional stream filter: `?cell=<hex-cell-id>&kind=<effect-kind>`.
#[derive(Clone, Debug, Default, Deserialize)]
pub struct StreamFilter {
    pub cell: Option<String>,
    pub kind: Option<String>,
}

/// One committed receipt on the wire. The summary fields are for curl /
/// dashboards; `receipt` is the full canonical [`dregg_turn::TurnReceipt`]
/// so the SDK can yield the public `Receipt` noun without a second fetch.
#[derive(Debug, Serialize)]
pub struct ReceiptEvent {
    /// Position in the node's receipt chain — the SSE `id` / resume cursor.
    pub chain_index: u64,
    pub receipt_hash: String,
    pub turn_hash: String,
    /// Cells this commit touched (agent cell, event-emitting cells, and the
    /// commit record's cell), hex-encoded, deduplicated.
    pub cells: Vec<String>,
    /// Effect-kind summaries from the commit record (empty when the commit
    /// path recorded none — e.g. blocklace-finalized turns).
    pub kinds: Vec<String>,
    /// Block height at commit when recorded; 0 when unknown.
    pub height: u64,
    /// Whether a STARK attestation is attached *right now* (witnessed
    /// receipt or persisted full-turn proof). Proofs land asynchronously.
    pub has_proof: bool,
    pub proof_status: crate::state::ActivityProofStatus,
    pub finality: String,
    pub timestamp: i64,
    /// The full canonical receipt.
    pub receipt: dregg_turn::TurnReceipt,
}

pub(crate) fn receipt_event_at(s: &NodeStateInner, idx: usize) -> Option<ReceiptEvent> {
    let r = s.cclerk.receipt_chain().get(idx)?;
    let receipt_hash = r.receipt_hash();
    let turn_hash = hex_encode(&r.turn_hash);

    let mut cells = vec![hex_encode(&r.agent.0)];
    for ev in &r.emitted_events {
        let cell = hex_encode(&ev.cell.0);
        if !cells.contains(&cell) {
            cells.push(cell);
        }
    }
    let mut kinds = Vec::new();
    let mut height = 0;
    if let Some(committed) = s.event_log.iter().rev().find(|e| e.turn_hash == turn_hash) {
        height = committed.height;
        if !cells.contains(&committed.cell_id) {
            cells.push(committed.cell_id.clone());
        }
        kinds = committed.effects.clone();
    }

    let stored_proof = s
        .store
        .get_config(&crate::turn_proving::turn_proof_config_key(&turn_hash))
        .ok()
        .flatten()
        .is_some();
    let has_proof = s.witnessed_receipt_count(&receipt_hash) > 0 || stored_proof;

    Some(ReceiptEvent {
        chain_index: idx as u64,
        receipt_hash: hex_encode(&receipt_hash),
        turn_hash,
        cells,
        kinds,
        height,
        has_proof,
        proof_status: crate::api::receipt_proof_status(s, r),
        finality: format!("{:?}", r.finality).to_lowercase(),
        timestamp: r.timestamp,
        receipt: r.clone(),
    })
}

fn matches(filter: &StreamFilter, ev: &ReceiptEvent) -> bool {
    if let Some(cell) = &filter.cell
        && !ev.cells.iter().any(|c| c.eq_ignore_ascii_case(cell))
    {
        return false;
    }
    if let Some(kind) = &filter.kind {
        let hit = ev.kinds.iter().any(|k| {
            k.eq_ignore_ascii_case(kind)
                || k.split(':')
                    .next()
                    .is_some_and(|p| p.eq_ignore_ascii_case(kind))
        });
        if !hit {
            return false;
        }
    }
    true
}

struct LiveCursor {
    state: NodeState,
    rx: broadcast::Receiver<NodeEvent>,
    filter: StreamFilter,
    /// Next chain index to send.
    next: u64,
    /// Admission slot held for the stream's lifetime (ANON-DoS #3): released on
    /// disconnect when the stream — and this cursor — is dropped.
    _slot: SseSlot,
}

/// The stream's driving state: either a rejected connection (over the SSE
/// admission caps — emits one error event then closes) or a live receipt cursor.
enum Cursor {
    Rejected { emitted: bool },
    Live(LiveCursor),
}

/// `GET /api/events/stream` — SSE of committed receipts.
pub async fn events_stream(
    Query(filter): Query<StreamFilter>,
    headers: HeaderMap,
    ConnectInfo(addr): ConnectInfo<std::net::SocketAddr>,
    State(state): State<NodeState>,
    limits: SseLimits,
) -> Sse<impl Stream<Item = Result<Event, Infallible>>> {
    // ANON-DoS #3: admit under the global + per-IP live-connection caps BEFORE
    // subscribing or touching state. A rejected connection returns a stream that
    // emits one error event and closes — it never holds a broadcast receiver or
    // re-acquires the read lock.
    let cursor = match limits.try_admit(addr.ip()) {
        None => Cursor::Rejected { emitted: false },
        Some(slot) => {
            // Subscribe BEFORE reading the chain head: anything committed between
            // the snapshot and the first recv() still wakes the cursor.
            let rx = state.subscribe_events();

            // `Last-Event-ID: <chain_index>` resumes after the last delivered
            // receipt; a fresh connection tails from the current head.
            let resume = headers
                .get("last-event-id")
                .and_then(|v| v.to_str().ok())
                .and_then(|v| v.trim().parse::<u64>().ok());
            let next = match resume {
                Some(id) => id.saturating_add(1),
                None => state.read().await.cclerk.receipt_chain_length() as u64,
            };
            Cursor::Live(LiveCursor {
                state,
                rx,
                filter,
                next,
                _slot: slot,
            })
        }
    };
    let stream = futures_util::stream::unfold(cursor, |cursor| async move {
        let mut c = match cursor {
            Cursor::Rejected { emitted: true } => return None,
            Cursor::Rejected { emitted: false } => {
                let sse = Event::default().event("error").data(
                    "{\"error\":\"too many concurrent event-stream connections; retry later\"}",
                );
                return Some((Ok::<_, Infallible>(sse), Cursor::Rejected { emitted: true }));
            }
            Cursor::Live(c) => c,
        };
        loop {
            // Drain the chain from the cursor before waiting again.
            let pending = {
                let s = c.state.read().await;
                let len = s.cclerk.receipt_chain_length() as u64;
                if c.next < len {
                    let ev = receipt_event_at(&s, c.next as usize);
                    c.next += 1;
                    Some(ev)
                } else {
                    None
                }
            };
            match pending {
                Some(Some(ev)) => {
                    if !matches(&c.filter, &ev) {
                        continue;
                    }
                    let sse = Event::default()
                        .event("receipt")
                        .id(ev.chain_index.to_string())
                        .data(
                            serde_json::to_string(&ev)
                                .unwrap_or_else(|e| format!("{{\"error\":\"serialize: {e}\"}}")),
                        );
                    return Some((Ok::<_, Infallible>(sse), Cursor::Live(c)));
                }
                Some(None) => continue,
                None => {}
            }
            // Chain drained — sleep on the broadcast until the next commit.
            match c.rx.recv().await {
                Ok(NodeEvent::Receipt { .. }) => continue,
                Ok(_) => continue,
                // Lag is harmless: the chain cursor catches up above.
                Err(broadcast::error::RecvError::Lagged(_)) => continue,
                Err(broadcast::error::RecvError::Closed) => return None,
            }
        }
    });

    // Heartbeat comment every 30s so proxies keep the stream open.
    Sse::new(stream).keep_alive(
        KeepAlive::new()
            .interval(Duration::from_secs(30))
            .text("hb"),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    /// ANON-DoS #3 FALSIFIER — both directions. The SSE admission control BOUNDS
    /// live connections by BOTH a per-IP cap and a global pool (a flood is
    /// refused), AND every admitted slot RELEASES its global permit + per-IP unit
    /// on drop (disconnect), so a legit client always reconnects once capacity
    /// frees (liveness).
    #[test]
    fn sse_admission_bounds_global_and_per_ip_and_releases_on_disconnect() {
        // Global pool of 3 live streams; per-IP cap of 2.
        let limits = SseLimits::new(3, 2);
        let ip_a: IpAddr = "10.0.0.1".parse().unwrap();
        let ip_b: IpAddr = "10.0.0.2".parse().unwrap();
        let ip_c: IpAddr = "10.0.0.3".parse().unwrap();

        // ip_a fills its per-IP budget (2), then its 3rd is refused — WITHOUT
        // consuming a global permit (the refused attempt returns it).
        let a1 = limits.try_admit(ip_a).expect("a1 admitted");
        let a2 = limits.try_admit(ip_a).expect("a2 admitted");
        assert!(
            limits.try_admit(ip_a).is_none(),
            "a single IP cannot exceed its per-IP cap"
        );

        // ip_b takes the last global permit; the global pool (3) is now full.
        let b1 = limits.try_admit(ip_b).expect("b1 admitted");
        assert!(
            limits.try_admit(ip_c).is_none(),
            "a fresh IP is refused once the GLOBAL pool is exhausted"
        );

        // LIVENESS: dropping a live slot (disconnect) frees a global permit AND
        // ip_a's per-IP unit, so a new connection is admitted again.
        drop(a1);
        let c1 = limits
            .try_admit(ip_c)
            .expect("a freed global permit admits a new connection");
        // ip_a is back under its per-IP cap too (a1 released), so it re-admits.
        drop(b1);
        let a3 = limits
            .try_admit(ip_a)
            .expect("ip_a re-admits after release");

        drop((a2, c1, a3));
    }
}
