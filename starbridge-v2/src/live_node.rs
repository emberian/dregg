//! The LIVE node connection — a real HTTP+SSE link to a running dregg node.
//!
//! Starbridge v2's headline capability is the EMBEDDED world ([`crate::world`]):
//! the verified executor runs in-process. But the master interface can ALSO
//! connect to a remote node/federation — to watch a live federation's receipt
//! nervous system, reflect its cells, and (designed-pending) submit turns to it.
//! That is THIS module.
//!
//! It is built in two layers, and the split is deliberate so the heart is
//! `cargo test`-able with NO network and NO gpui:
//!
//!   * **Pure (always compiled, fully testable):**
//!     - [`SseParser`] — the `text/event-stream` line-framing decoder. The node's
//!       `/api/events/stream` ([`node/src/events.rs`]) emits `event: receipt`,
//!       `id: <chain_index>`, `data: <json>` records separated by blank lines,
//!       with `: hb` heartbeat comments. [`SseParser::push`] feeds it bytes and
//!       yields complete [`crate::model::ReceiptEvent`]s as they close — the SAME
//!       drain a live socket would produce, driven from a fixture in a test.
//!     - [`LiveReflection`] — projects a node's wire snapshots (`/status`,
//!       `/api/cells`, `/api/receipts`) into the SAME uniform
//!       [`reflect::Inspectable`] model the embedded world uses, so the cockpit's
//!       inspector renders a live REMOTE cell/receipt identically to a local one —
//!       no parallel view path.
//!     - [`ReceiptFeed`] — the cursor + resume model. It tracks the last delivered
//!       `chain_index` (the SSE `Last-Event-ID`), appends drained receipts to a
//!       bounded ring, and reports how many are NEW since the last poll — which is
//!       exactly the signal the cockpit turns into a `cx.notify()` per receipt
//!       (replacing the old static snapshot).
//!
//!   * **I/O (gated on the `live-node` feature — pulls `reqwest`):** the actual
//!     byte pull. [`LiveNode::sync`] does the blocking snapshot reads; the SSE
//!     stream is driven by feeding the socket's chunks into the pure [`SseParser`]
//!     on a background reader (the cockpit owns the thread + a channel, so the
//!     gpui side stays single-threaded and just drains the channel under
//!     `cx.notify()`). Keeping the parse pure means the live SSE wiring is the
//!     SAME code the tests exercise — only the byte source differs.
//!
//! gpui-free. The pure layer compiles + tests under just `embedded-executor`.

use crate::model::{CellListEntry, NodeStatus, ReceiptEvent, VatEntry};
use crate::reflect::{Field, FieldValue, Inspectable, ObjectKind};

// ===========================================================================
// SSE PARSER — the pure text/event-stream decoder (testable with byte fixtures)
// ===========================================================================

/// A streaming decoder for the node's `GET /api/events/stream` SSE wire format.
///
/// SSE framing (`node/src/events.rs` emits, per the W3C event-stream grammar):
/// records are separated by a blank line; within a record, `field: value` lines
/// accumulate (`event`, `id`, `data`). A leading `:` is a comment (the node sends
/// `: hb` keep-alives) and is ignored. We collect the `data` field(s) of each
/// record and, when the record closes, parse the JSON into a [`ReceiptEvent`].
///
/// This is a pure state machine: [`SseParser::push`] takes a byte chunk (a socket
/// read of any size — records may split across chunks) and returns the
/// [`ReceiptEvent`]s that COMPLETED in this chunk. A test drives it from a `&[u8]`
/// fixture; the live reader drives it from socket chunks. Same code.
#[derive(Default)]
pub struct SseParser {
    /// Bytes received but not yet split into complete lines.
    buf: Vec<u8>,
    /// The `event:` field of the record currently being assembled.
    cur_event: Option<String>,
    /// The `id:` field (the chain-index resume cursor) of the current record.
    cur_id: Option<String>,
    /// Accumulated `data:` payload of the current record (SSE allows multiple
    /// `data:` lines; they join with `\n`).
    cur_data: String,
    /// Whether the current record has seen any field at all (so a stray blank
    /// line before the first field doesn't emit an empty record).
    in_record: bool,
}

/// A parsed SSE record that decoded to a receipt event, plus its resume id.
#[derive(Debug, Clone)]
pub struct SseRecord {
    /// The SSE `id:` (the node's `chain_index`) — the `Last-Event-ID` resume
    /// cursor for a reconnect.
    pub id: Option<u64>,
    /// The decoded receipt event.
    pub event: ReceiptEvent,
}

impl SseParser {
    pub fn new() -> Self {
        Self::default()
    }

    /// Feed a chunk of bytes from the stream; return every record that COMPLETED.
    ///
    /// Records that span chunk boundaries are retained internally until their
    /// terminating blank line arrives. A `data:` payload that fails to parse as a
    /// [`ReceiptEvent`] (e.g. the node's `{"error":...}` fallback) is dropped
    /// rather than aborting the stream — a live feed must survive one bad frame.
    pub fn push(&mut self, chunk: &[u8]) -> Vec<SseRecord> {
        self.buf.extend_from_slice(chunk);
        let mut out = Vec::new();
        // Split on '\n'; keep the trailing partial line in `buf`.
        while let Some(nl) = self.buf.iter().position(|&b| b == b'\n') {
            let line_bytes: Vec<u8> = self.buf.drain(..=nl).collect();
            // Strip the trailing '\n' (and a '\r' if the node used CRLF).
            let mut line = &line_bytes[..line_bytes.len() - 1];
            if line.last() == Some(&b'\r') {
                line = &line[..line.len() - 1];
            }
            if let Some(rec) = self.feed_line(line) {
                out.push(rec);
            }
        }
        out
    }

    /// Process one complete (newline-stripped) line; emit a record on dispatch
    /// (a blank line closing a non-empty record).
    fn feed_line(&mut self, line: &[u8]) -> Option<SseRecord> {
        if line.is_empty() {
            // Blank line: dispatch the current record (if any field was seen).
            if self.in_record {
                return self.dispatch();
            }
            return None;
        }
        // A line starting with ':' is a comment (the heartbeat `: hb`) — ignore.
        if line[0] == b':' {
            return None;
        }
        self.in_record = true;
        // Split into `field` and `value` on the first ':'; per spec a single
        // space after the colon is stripped.
        let (field, value) = match line.iter().position(|&b| b == b':') {
            Some(i) => {
                let field = String::from_utf8_lossy(&line[..i]).into_owned();
                let mut v = &line[i + 1..];
                if v.first() == Some(&b' ') {
                    v = &v[1..];
                }
                (field, String::from_utf8_lossy(v).into_owned())
            }
            // A field with no ':' is a field name with an empty value.
            None => (String::from_utf8_lossy(line).into_owned(), String::new()),
        };
        match field.as_str() {
            "event" => self.cur_event = Some(value),
            "id" => self.cur_id = Some(value),
            "data" => {
                if !self.cur_data.is_empty() {
                    self.cur_data.push('\n');
                }
                self.cur_data.push_str(&value);
            }
            _ => {} // retry:, or unknown fields — ignored.
        }
        None
    }

    /// Close the current record: parse its accumulated `data` as a receipt event.
    fn dispatch(&mut self) -> Option<SseRecord> {
        let data = std::mem::take(&mut self.cur_data);
        let id = self
            .cur_id
            .take()
            .and_then(|s| s.trim().parse::<u64>().ok());
        // The node tags receipt records `event: receipt`; tolerate a missing
        // event field (default-named records still carry receipt JSON).
        let event_name = self.cur_event.take();
        self.in_record = false;
        let is_receipt = event_name
            .as_deref()
            .map(|e| e == "receipt")
            .unwrap_or(true);
        if !is_receipt || data.is_empty() {
            return None;
        }
        match serde_json::from_str::<ReceiptEvent>(&data) {
            Ok(event) => Some(SseRecord { id, event }),
            // A bad frame (e.g. the node's serialize-error fallback) is dropped,
            // not fatal — the chain cursor catches up on the next good record.
            Err(_) => None,
        }
    }
}

// ===========================================================================
// LIVE REFLECTION — project a remote node's wire snapshots into Inspectable
// ===========================================================================

/// Projects a remote node's wire types into the SAME uniform
/// [`reflect::Inspectable`] the embedded world produces — so a view renders a
/// LIVE remote cell/receipt/status with the exact same field tree it renders a
/// local one. No parallel view path: the cockpit's inspector is backend-agnostic.
pub struct LiveReflection;

impl LiveReflection {
    /// Project a remote cell list entry (`GET /api/cells`) into an [`Inspectable`].
    /// The id/balance/nonce/caps/delegate/program fields map straight onto the
    /// same `Field` rows the embedded `reflect::reflect_cell` emits.
    pub fn reflect_cell_entry(entry: &CellListEntry) -> Inspectable {
        let id_bytes = hex32(&entry.id);
        let fields = vec![
            Field {
                key: "id".into(),
                value: FieldValue::Id(id_bytes),
            },
            Field::balance("balance", entry.balance),
            Field::count("nonce", entry.nonce),
            Field::count("capabilities", entry.capability_count as u64),
            Field::boolean("has_delegate", entry.has_delegate),
            Field::boolean("has_program", entry.has_program),
            Field::boolean("found", entry.found),
            Field::text("source", "live node".to_string()),
        ];
        Inspectable {
            kind: ObjectKind::Cell,
            title: format!("Cell {}", crate::reflect::short_hex(&id_bytes)),
            subtitle: format!(
                "live · balance {} · {} caps",
                entry.balance, entry.capability_count
            ),
            fields,
        }
    }

    /// Project a streamed receipt event (`GET /api/events/stream`) into an
    /// [`Inspectable`] — the live provenance node. Mirrors the local
    /// `reflect::reflect_receipt` shape over the summary fields the wire carries.
    pub fn reflect_receipt_event(ev: &ReceiptEvent) -> Inspectable {
        let mut fields = vec![
            Field {
                key: "receipt_hash".into(),
                value: FieldValue::Hash(hex32(&ev.receipt_hash)),
            },
            Field {
                key: "turn_hash".into(),
                value: FieldValue::Hash(hex32(&ev.turn_hash)),
            },
            Field::count("chain_index", ev.chain_index),
            Field::count("height", ev.height),
            Field::boolean("has_proof", ev.has_proof),
            Field::text("finality", ev.finality.clone()),
            Field::text("timestamp", ev.timestamp.to_string()),
            Field::count("cells_touched", ev.cells.len() as u64),
        ];
        for (i, c) in ev.cells.iter().enumerate() {
            fields.push(Field {
                key: format!("cell[{i}]"),
                value: FieldValue::Id(hex32(c)),
            });
        }
        if !ev.kinds.is_empty() {
            fields.push(Field::text("kinds", ev.kinds.join(", ")));
        }
        Inspectable {
            kind: ObjectKind::Receipt,
            title: format!(
                "Receipt {}",
                crate::reflect::short_hex(&hex32(&ev.receipt_hash))
            ),
            subtitle: format!(
                "live · #{} · h{} · {}",
                ev.chain_index, ev.height, ev.finality
            ),
            fields,
        }
    }

    /// Project a **Dregg Computer** (a `GET /v1/vats` roster row) into an
    /// [`Inspectable`] — the vat rendered with the SAME field tree every other
    /// object gets, because the vat IS a cell (`ObjectKind::Image`: a whole
    /// World checkpointable to one committed root, not a single ledger cell).
    /// The subtitle carries the one-glance rental truths: lifecycle, funded
    /// admission, settle count, and the witness discipline.
    pub fn reflect_vat_entry(v: &VatEntry) -> Inspectable {
        let mode = if v.witness_mode.is_empty() {
            "full" // unknown wire value decodes to the safe default, like WitnessMode::from_u8
        } else {
            v.witness_mode.as_str()
        };
        let mut fields = vec![
            Field {
                key: "cell_id".into(),
                value: FieldValue::Id(hex32(&v.cell_id)),
            },
            Field::text("name", v.name.clone()),
            Field::text("owner", v.owner.clone()),
            Field::text("state", v.state.clone()),
            Field::boolean("funded", v.funded),
            Field::count("paid_periods", v.paid_periods),
            Field::text("witness_mode", mode.to_string()),
            Field::text(
                "cap_scope",
                format!("vat:{}", crate::model::short_id(&v.cell_id)),
            ),
        ];
        match &v.endpoint {
            Some(url) => fields.push(Field::text("endpoint", url.clone())),
            None => fields.push(Field::text("endpoint", "(not reachable)".to_string())),
        }
        if let Some(root) = &v.checkpoint_root {
            fields.push(Field {
                key: "checkpoint_root".into(),
                value: FieldValue::Hash(hex32(root)),
            });
        }
        Inspectable {
            kind: ObjectKind::Image,
            title: format!(
                "Dregg Computer '{}' {}",
                if v.name.is_empty() { "?" } else { &v.name },
                crate::model::short_id(&v.cell_id)
            ),
            subtitle: format!(
                "{} · {} · {} period(s) settled · {}",
                if v.state.is_empty() {
                    "unknown"
                } else {
                    &v.state
                },
                if v.funded { "funded" } else { "UNFUNDED" },
                v.paid_periods,
                mode,
            ),
            fields,
        }
    }

    /// Project a node's `/status` into an [`Inspectable`] (the distribution axis,
    /// remote half): liveness, the producer (lean vs rust — surfaced honestly), the
    /// peer/height/dag counts.
    pub fn reflect_status(base_url: &str, s: &NodeStatus) -> Inspectable {
        Inspectable {
            kind: ObjectKind::Image,
            title: format!("Live node — {base_url}"),
            subtitle: format!(
                "{} · producer {} · h{} · {} peers",
                if s.healthy { "healthy" } else { "DOWN" },
                s.state_producer,
                s.latest_height,
                s.peer_count
            ),
            fields: vec![
                Field::boolean("healthy", s.healthy),
                Field::count("peer_count", s.peer_count as u64),
                Field::count("latest_height", s.latest_height),
                Field::count("dag_height", s.dag_height),
                Field::boolean("consensus_live", s.consensus_live),
                Field::text("federation_mode", s.federation_mode.clone()),
                Field::text("state_producer", s.state_producer.clone()),
                Field::boolean("lean_producer", s.lean_producer),
                Field::boolean("full_turn_proving", s.full_turn_proving),
                Field::count("covered_effects", s.producer_covered_effects as u64),
            ],
        }
    }
}

// ===========================================================================
// RECEIPT FEED — the cursor + resume + new-since-last-poll model
// ===========================================================================

/// The live receipt feed: a bounded ring of streamed receipts + the resume
/// cursor. This is the piece that REPLACES the static snapshot — the cockpit
/// drains [`ReceiptFeed::take_new`] each frame and fires a `cx.notify()` for each
/// freshly-arrived receipt (so the ReceiptInspector advances live, not on reload).
///
/// The cursor (`last_id`) is the SSE `Last-Event-ID`: on a reconnect the reader
/// sends it so the stream resumes after the last delivered chain index (the node
/// guarantees at-least-once across reconnects; the ring dedups by `chain_index`).
pub struct ReceiptFeed {
    /// The receipts received so far, newest last, bounded to `cap`.
    ring: Vec<ReceiptEvent>,
    /// Max retained receipts (a live feed is unbounded; the UI shows a tail).
    cap: usize,
    /// The highest `chain_index` delivered — the resume cursor + the dedup key.
    last_id: Option<u64>,
    /// Count of receipts appended since the last [`ReceiptFeed::take_new`] — the
    /// `cx.notify()` budget.
    pending_new: usize,
}

impl ReceiptFeed {
    /// A feed retaining the last `cap` receipts (e.g. 256 for the inspector tail).
    pub fn new(cap: usize) -> Self {
        ReceiptFeed {
            ring: Vec::new(),
            cap: cap.max(1),
            last_id: None,
            pending_new: 0,
        }
    }

    /// Ingest a streamed receipt. Deduplicates by `chain_index` (the node may
    /// re-deliver across a reconnect), advances the resume cursor, and bumps the
    /// pending-notify count. Returns `true` if it was NEW (not a duplicate).
    pub fn ingest(&mut self, ev: ReceiptEvent) -> bool {
        // Dedup: anything at-or-below the cursor we have already shown.
        if let Some(last) = self.last_id {
            if ev.chain_index <= last {
                return false;
            }
        }
        self.last_id = Some(ev.chain_index);
        self.ring.push(ev);
        if self.ring.len() > self.cap {
            let overflow = self.ring.len() - self.cap;
            self.ring.drain(..overflow);
        }
        self.pending_new += 1;
        true
    }

    /// Ingest a batch (e.g. the records the [`SseParser`] drained from one chunk).
    /// Returns how many were new.
    pub fn ingest_records(&mut self, records: impl IntoIterator<Item = SseRecord>) -> usize {
        let mut n = 0;
        for rec in records {
            if self.ingest(rec.event) {
                n += 1;
            }
        }
        n
    }

    /// The resume cursor for the next connection's `Last-Event-ID` header.
    pub fn resume_cursor(&self) -> Option<u64> {
        self.last_id
    }

    /// The retained receipt tail (newest last).
    pub fn receipts(&self) -> &[ReceiptEvent] {
        &self.ring
    }

    /// The most recent receipt, if any (what the inspector focuses by default).
    pub fn latest(&self) -> Option<&ReceiptEvent> {
        self.ring.last()
    }

    /// Drain the pending-new count (the cockpit calls this each frame; the return
    /// is how many `cx.notify()`-worthy receipts arrived since the last drain).
    /// Resets the counter to zero.
    pub fn take_new(&mut self) -> usize {
        std::mem::take(&mut self.pending_new)
    }

    /// Whether there are undrained new receipts (a cheap check before draining).
    pub fn has_new(&self) -> bool {
        self.pending_new > 0
    }
}

/// Decode a hex id (any length) into a 32-byte array, left-aligned + zero-padded
/// (and truncated if longer). Tolerant: a malformed live id renders as zeros
/// rather than panicking the view.
fn hex32(s: &str) -> [u8; 32] {
    let mut out = [0u8; 32];
    if let Ok(bytes) = hex::decode(s) {
        let n = bytes.len().min(32);
        out[..n].copy_from_slice(&bytes[..n]);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A canonical receipt-event JSON the node's SSE stream emits (the summary
    /// fields of `events::ReceiptEvent`, matching `crate::model::ReceiptEvent`).
    fn receipt_json(idx: u64, hash_byte: &str) -> String {
        format!(
            r#"{{"chain_index":{idx},"receipt_hash":"{h}","turn_hash":"{t}","cells":["{c}"],"kinds":["transfer"],"height":{ht},"has_proof":true,"finality":"final","timestamp":1718000000}}"#,
            h = hash_byte.repeat(32),
            t = "cd".repeat(32),
            c = "11".repeat(32),
            ht = 1880 + idx,
        )
    }

    #[test]
    fn sse_parser_decodes_a_single_record() {
        let mut p = SseParser::new();
        let frame = format!("event: receipt\nid: 7\ndata: {}\n\n", receipt_json(7, "ab"));
        let recs = p.push(frame.as_bytes());
        assert_eq!(recs.len(), 1);
        assert_eq!(recs[0].id, Some(7));
        assert_eq!(recs[0].event.chain_index, 7);
        assert!(recs[0].event.has_proof);
    }

    #[test]
    fn sse_parser_handles_chunk_splits_and_heartbeats() {
        // (a) A record split across THREE arbitrary byte boundaries (a real socket
        // hands back chunks of any size, splitting lines) — the parser buffers the
        // partial lines and reassembles. No record completes until the final chunk.
        let mut p = SseParser::new();
        let body = receipt_json(3, "ef");
        let full = format!("event: receipt\nid: 3\ndata: {body}\n\n");
        let bytes = full.as_bytes();
        let third = bytes.len() / 3;
        assert!(p.push(&bytes[..third]).is_empty());
        assert!(p.push(&bytes[third..2 * third]).is_empty());
        let recs = p.push(&bytes[2 * third..]);
        assert_eq!(recs.len(), 1);
        assert_eq!(recs[0].event.chain_index, 3);

        // (b) A heartbeat comment (`: hb`) the node sends between records, at a
        // record boundary, is ignored — and a following record still decodes (the
        // stream survives keep-alives interleaved with receipts).
        let mut p2 = SseParser::new();
        assert!(p2.push(b": hb\n").is_empty()); // a bare heartbeat — no record
        let rec_frame = format!("event: receipt\nid: 4\ndata: {}\n\n", receipt_json(4, "ab"));
        let recs2 = p2.push(rec_frame.as_bytes());
        assert_eq!(recs2.len(), 1);
        assert_eq!(recs2[0].event.chain_index, 4);
    }

    #[test]
    fn sse_parser_drops_a_bad_frame_without_aborting() {
        let mut p = SseParser::new();
        // A serialize-error fallback frame (the node's `{"error":...}`) — dropped.
        let bad = "event: receipt\nid: 1\ndata: {\"error\":\"serialize: boom\"}\n\n";
        assert!(p.push(bad.as_bytes()).is_empty());
        // A good frame right after still decodes (the stream survived the bad one).
        let good = format!("event: receipt\nid: 2\ndata: {}\n\n", receipt_json(2, "ab"));
        let recs = p.push(good.as_bytes());
        assert_eq!(recs.len(), 1);
        assert_eq!(recs[0].event.chain_index, 2);
    }

    #[test]
    fn receipt_feed_dedups_resumes_and_counts_new() {
        let mut feed = ReceiptFeed::new(8);
        // Parse three records off a stream and ingest them.
        let mut p = SseParser::new();
        let mut frames = String::new();
        for (idx, b) in [(0u64, "00"), (1, "11"), (2, "22")] {
            frames.push_str(&format!(
                "event: receipt\nid: {idx}\ndata: {}\n\n",
                receipt_json(idx, b)
            ));
        }
        let recs = p.push(frames.as_bytes());
        assert_eq!(feed.ingest_records(recs), 3);
        assert_eq!(feed.resume_cursor(), Some(2));
        // The cockpit drains the notify budget: three new receipts arrived.
        assert_eq!(feed.take_new(), 3);
        assert_eq!(feed.take_new(), 0); // drained
        assert!(!feed.has_new());

        // A RECONNECT re-delivers index 2 (at-least-once) + a fresh index 3. The
        // feed dedups 2 and counts only 3 as new — the resume cursor advances.
        let mut p2 = SseParser::new();
        let reframe = format!(
            "event: receipt\nid: 2\ndata: {}\n\nevent: receipt\nid: 3\ndata: {}\n\n",
            receipt_json(2, "22"),
            receipt_json(3, "33"),
        );
        let recs2 = p2.push(reframe.as_bytes());
        assert_eq!(feed.ingest_records(recs2), 1); // only #3 is new
        assert_eq!(feed.resume_cursor(), Some(3));
        assert_eq!(feed.latest().unwrap().chain_index, 3);
        assert_eq!(feed.take_new(), 1);
    }

    #[test]
    fn receipt_feed_bounds_the_ring() {
        let mut feed = ReceiptFeed::new(2);
        for idx in 0..5u64 {
            feed.ingest(ev(idx));
        }
        // Only the last 2 retained; the cursor still tracks the head.
        assert_eq!(feed.receipts().len(), 2);
        assert_eq!(feed.receipts()[0].chain_index, 3);
        assert_eq!(feed.receipts()[1].chain_index, 4);
        assert_eq!(feed.resume_cursor(), Some(4));
    }

    fn ev(idx: u64) -> ReceiptEvent {
        ReceiptEvent {
            chain_index: idx,
            receipt_hash: "ab".repeat(32),
            turn_hash: "cd".repeat(32),
            cells: vec!["11".repeat(32)],
            kinds: vec!["transfer".into()],
            height: 1880 + idx,
            has_proof: idx.is_multiple_of(2),
            finality: "final".into(),
            timestamp: 1_718_000_000 + idx as i64,
        }
    }

    #[test]
    fn live_reflection_matches_the_uniform_inspectable_shape() {
        // A live cell reflects into the SAME ObjectKind::Cell the embedded world
        // produces — the inspector is backend-agnostic.
        let entry = CellListEntry {
            id: "11".repeat(32),
            balance: 100_000,
            nonce: 12,
            capability_count: 3,
            has_delegate: true,
            has_program: false,
            found: true,
        };
        let insp = LiveReflection::reflect_cell_entry(&entry);
        assert_eq!(insp.kind, ObjectKind::Cell);
        assert!(insp.fields.iter().any(|f| f.key == "balance"));
        assert!(insp
            .fields
            .iter()
            .any(|f| matches!(f.value, FieldValue::Id(_))));

        let receipt = ev(9);
        let rinsp = LiveReflection::reflect_receipt_event(&receipt);
        assert_eq!(rinsp.kind, ObjectKind::Receipt);
        assert!(rinsp
            .fields
            .iter()
            .any(|f| matches!(f.value, FieldValue::Hash(_))));
    }

    /// A vat reflects into the SAME uniform Inspectable — a running one carries
    /// its endpoint, a sleeping one its committed checkpoint root, and an empty
    /// witness_mode decodes to the safe "full" default (the `WitnessMode::from_u8`
    /// discipline held on the string wire form too).
    #[test]
    fn vat_reflection_carries_the_rental_truths() {
        let vats = crate::client::mock::vats();
        let running = LiveReflection::reflect_vat_entry(&vats[0]);
        assert_eq!(running.kind, ObjectKind::Image);
        assert!(running.title.contains("mybox"));
        assert!(running.subtitle.contains("funded"));
        assert!(running.fields.iter().any(|f| f.key == "endpoint"
            && matches!(&f.value, FieldValue::Text(t) if t.starts_with("http"))));
        assert!(
            running.fields.iter().any(|f| f.key == "cap_scope"
                && matches!(&f.value, FieldValue::Text(t) if t.starts_with("vat:"))),
            "the vat names its own capability scope"
        );

        let sleeping = LiveReflection::reflect_vat_entry(&vats[1]);
        assert!(
            sleeping
                .fields
                .iter()
                .any(|f| f.key == "checkpoint_root" && matches!(f.value, FieldValue::Hash(_))),
            "a sleeping vat IS its committed root"
        );

        let unknown_mode = LiveReflection::reflect_vat_entry(&crate::model::VatEntry {
            cell_id: "aa".repeat(32),
            ..Default::default()
        });
        assert!(
            unknown_mode.fields.iter().any(|f| f.key == "witness_mode"
                && matches!(&f.value, FieldValue::Text(t) if t == "full")),
            "an unknown witness mode defaults SAFE (full), never symbolic"
        );
    }
}
