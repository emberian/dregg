//! **The live receipt-stream primitive** — a surface subscribes to the node's
//! committing receipt feed and reflects it LIVE (the "cockpit goes LIVE"
//! foundation, `.docs-history-noclaude/NEXT-WAVE.md` item D).
//!
//! ## What this is
//!
//! Today a surface's organs (channel / mailbox / court) are SNAPSHOTS — a
//! point-in-time read of the node. This module is the primitive that makes them
//! **live reflections of the committing node**: a [`ReceiptStream`] is a
//! subscription over the node's `GET /api/events/stream` ([`node/src/events.rs`])
//! receipt nervous system, and each committed receipt arrives as a
//! [`StreamedReceipt`] — one observed world transition (a committed turn),
//! `WorldEvent`-shaped (the crate-boundary analogue of the cockpit's
//! `WorldEvent::TurnCommitted` projection, but carrying the REAL receipt).
//!
//! It is built on the GENUINE receipt-chain shapes — it reinvents NONE of them:
//!
//!   * the wire envelope is [`dregg_query::ReceiptEventRow`] (the crate's
//!     already-canonical, transport-agnostic mirror of `events::ReceiptEvent`),
//!     extended with the full canonical [`dregg_turn::TurnReceipt`] the SSE frame's
//!     `data:` payload carries in its `receipt` field — so the stream item is the
//!     genuine committed receipt, not a parallel summary;
//!   * the cursor is the dense `chain_index` — the SAME value the node serves as
//!     the SSE `id:` / `Last-Event-ID` resume header, and the SAME monotone
//!     `since(cursor)` discipline the cockpit's `Dynamics` log already uses;
//!   * forge-detection is the REAL [`dregg_turn::TurnReceipt::receipt_hash`]
//!     (the canonical `dregg-receipt-v5` BLAKE3 digest) + the REAL
//!     [`dregg_types::merkle_root_of_receipt_hashes`] receipt-stream verifier the
//!     [`dregg_types::AttestedRoot`] binds — never a bespoke check.
//!
//! ## The three guarantees (the deliverable's named bar)
//!
//! 1. **A subscriber sees committed receipts IN ORDER.** [`ReceiptStream::ingest`]
//!    admits a receipt IFF its `chain_index` is the expected next DENSE position
//!    (the node's chain is dense + monotone). [`ReceiptStream::since`] /
//!    [`ReceiptStream::delivered`] then read the verified prefix newest-last.
//! 2. **A cursor RESUMES.** [`ReceiptStream::resume_cursor`] is the
//!    `Last-Event-ID` a reconnecting subscriber replays; a re-delivered receipt at
//!    or below the cursor is deduplicated (the node is at-least-once across
//!    reconnects), so resume is lossless and idempotent.
//! 3. **An out-of-order / FORGED item is REJECTED.** A gap or a rewind in
//!    `chain_index` is [`IngestError::OutOfOrder`]; a receipt whose body does not
//!    hash to its claimed `receipt_hash` (a tampered `receipt`, or a swapped hash)
//!    is [`IngestError::Forged`] — caught by recomputing the canonical
//!    `receipt_hash()` and comparing. A subscriber that ALSO holds the federation's
//!    [`dregg_types::AttestedRoot`] can verify the whole delivered prefix against
//!    its bound `receipt_stream_root` ([`ReceiptStream::verify_against`]).
//!
//! ## Pure core + the async edge (the executor seam, named not faked)
//!
//! The verification state machine ([`ReceiptStream::ingest`] / [`since`] /
//! [`next_ready`]) is PURE — no async, no runtime, always `cargo test`-able from a
//! fixture, exactly the discipline `dregg_query` and the cockpit's pure
//! `live_node::SseParser` keep. Behind the default `stream` feature it ALSO impls
//! [`futures_core::Stream`] over a fed queue, so the cockpit's gpui async executor
//! can `.await` a [`ReceiptStream`] (driving [`futures_core::Stream::poll_next`])
//! to advance the [`ReceiptInspector`] live — see the BUILD STATUS follow-on at the
//! foot of this file. This leaf crate carries NO HTTP / tokio dep itself (the byte
//! pull is the I/O lane's; only the parsed envelope crosses this boundary).

use std::collections::VecDeque;

use serde::Deserialize;

use dregg_query::client::ReceiptEventRow;
use dregg_turn::TurnReceipt;
use dregg_types::{merkle_root_of_receipt_hashes, AttestedRoot};

/// The dense receipt-chain cursor — a position in the node's receipt chain. This
/// IS the value the node serves as the SSE `id:` and accepts back as the
/// `Last-Event-ID` resume header, and the value the cockpit's `Dynamics::since`
/// cursor mirrors. A fresh subscription tails from the current head; a resuming
/// one replays the last delivered cursor.
///
/// `Cursor::origin()` is "before chain index 0" — the start a from-genesis
/// subscriber uses so the FIRST expected dense position is `0`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Cursor(pub u64);

impl Cursor {
    /// The cursor BEFORE the first chain entry (so the first expected dense
    /// `chain_index` is `0`). Represented as `u64::MAX` (the "nothing delivered
    /// yet" sentinel) so the first `next_expected()` wraps to `0`.
    pub const ORIGIN: Cursor = Cursor(u64::MAX);

    /// A cursor that has delivered through chain index `idx` (the `Last-Event-ID`
    /// after seeing the receipt at `idx`).
    pub fn delivered_through(idx: u64) -> Cursor {
        Cursor(idx)
    }

    /// The chain index this cursor expects NEXT (one past what it has delivered).
    /// At [`Cursor::ORIGIN`] this is `0` (the first dense position).
    pub fn next_expected(self) -> u64 {
        self.0.wrapping_add(1)
    }

    /// The `Last-Event-ID` header value a reconnecting subscriber sends to resume
    /// AFTER this cursor — `None` at origin (a fresh tail, no resume), else the
    /// last delivered chain index (the node resumes from `id + 1`).
    pub fn last_event_id(self) -> Option<u64> {
        if self == Cursor::ORIGIN {
            None
        } else {
            Some(self.0)
        }
    }
}

/// One streamed, **verified** committed receipt — the `WorldEvent`-shaped item a
/// subscriber receives. It is one observed world transition (a turn the node
/// committed), the crate-boundary analogue of the cockpit's
/// `WorldEvent::TurnCommitted`, but carrying the genuine canonical
/// [`dregg_turn::TurnReceipt`] (not a flattened summary) so a surface can render
/// the full provenance node and re-verify it third-party-checkably.
///
/// A [`StreamedReceipt`] only EXISTS once [`ReceiptStream::ingest`] has admitted
/// it (in-order + un-forged), so holding one is itself the evidence that the two
/// gates passed.
#[derive(Clone, Debug)]
pub struct StreamedReceipt {
    /// Unauthenticated policy hint, never validity evidence.
    pub proof_status: Option<String>,
    /// The dense chain position — the cursor / `Last-Event-ID` of this receipt.
    pub chain_index: u64,
    /// The canonical 32-byte receipt commitment (`TurnReceipt::receipt_hash()`),
    /// RECOMPUTED from the body at ingest — so this value is the verified one, not
    /// the (possibly forged) claimed string off the wire.
    pub receipt_hash: [u8; 32],
    /// Block height at commit (`0` when the node did not record one — e.g. a
    /// blocklace-finalized turn whose commit record carried no height).
    pub height: u64,
    /// Cells this commit touched (agent cell first, then event-emitting cells +
    /// the commit-record cell), hex-encoded — the summary the row carries.
    pub cells: Vec<String>,
    /// Effect-kind summaries from the commit record (empty when none recorded).
    pub kinds: Vec<String>,
    /// The full canonical receipt — the genuine committed object. Re-hashing this
    /// reproduces [`StreamedReceipt::receipt_hash`] (that equality is what
    /// [`ReceiptStream::ingest`] checked).
    pub receipt: TurnReceipt,
}

impl StreamedReceipt {
    /// A short human label for an activity feed (the `WorldEvent::label`
    /// analogue): "receipt #N @hH (K touched)".
    pub fn label(&self) -> String {
        format!(
            "receipt #{} @h{} ({} cell{} touched)",
            self.chain_index,
            self.height,
            self.cells.len(),
            if self.cells.len() == 1 { "" } else { "s" },
        )
    }
}

/// The wire envelope a subscriber feeds [`ReceiptStream::ingest`] — the SSE
/// frame's `data:` payload (`events::ReceiptEvent`) as this crate reads it.
///
/// It is built ON [`dregg_query::ReceiptEventRow`] (the canonical summary mirror —
/// `chain_index` / `receipt_hash` / `height` / `cells` / `kinds`, flattened in) and
/// adds exactly the field the forge-check needs that the summary row omits: the
/// full canonical `receipt`. So the envelope NAMES the query crate's row shape and
/// the genuine `TurnReceipt`; it invents no parallel summary. (`turn_hash` /
/// `has_proof` is not derivable from a signature. This primitive verifies receipt
/// identity only, never validity-proof coverage; `not_required` cannot grant it.)
#[derive(Clone, Debug, Deserialize)]
pub struct ReceiptEnvelope {
    /// Node policy hint, outside the canonical receipt and never verification evidence.
    /// `not_required` means signature attestation only.
    #[serde(default)]
    pub proof_status: Option<String>,
    /// The canonical summary fields — the EXACT [`ReceiptEventRow`] shape, flattened
    /// so the wire JSON deserializes into it directly.
    #[serde(flatten)]
    pub row: ReceiptEventRow,
    /// The full canonical receipt the SSE `data:` payload carries (the node's
    /// `ReceiptEvent::receipt`). The forge-check re-hashes THIS and compares to
    /// `row.receipt_hash`.
    pub receipt: TurnReceipt,
}

impl ReceiptEnvelope {
    /// Construct an envelope from a receipt + its summary, for tests / a producer
    /// that already holds the typed pieces. `receipt_hash` is taken as the CLAIMED
    /// string (hex of the bytes) — pass `receipt.receipt_hash()`'s hex for an honest
    /// frame, or a different value to model a forged one.
    pub fn new(
        chain_index: u64,
        receipt_hash_hex: String,
        height: u64,
        cells: Vec<String>,
        kinds: Vec<String>,
        receipt: TurnReceipt,
    ) -> Self {
        ReceiptEnvelope {
            proof_status: None,
            row: ReceiptEventRow {
                chain_index,
                receipt_hash: receipt_hash_hex,
                height,
                cells,
                kinds,
            },
            receipt,
        }
    }

    /// An HONEST envelope around `receipt` at `chain_index`: the claimed
    /// `receipt_hash` is exactly `receipt.receipt_hash()` (the canonical digest),
    /// so it passes the forge-check. The convenience a faithful producer / the
    /// node's own emit path uses.
    pub fn honest(chain_index: u64, height: u64, receipt: TurnReceipt) -> Self {
        let hash_hex = encode_hex(&receipt.receipt_hash());
        let cells = vec![encode_hex(receipt.agent.as_bytes())];
        Self::new(chain_index, hash_hex, height, cells, Vec::new(), receipt)
    }

    /// The claimed (wire) receipt hash decoded to bytes — `None` if it is not 32
    /// hex bytes (a malformed frame).
    fn claimed_hash_bytes(&self) -> Option<[u8; 32]> {
        decode_hex32(&self.row.receipt_hash)
    }
}

/// Why [`ReceiptStream::ingest`] refused a receipt.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IngestError {
    /// The receipt's `chain_index` is not the expected next dense position — a
    /// GAP (skipped a chain entry) or a REWIND (an index at/below the cursor that
    /// is not a benign at-least-once re-delivery of the immediate last). The
    /// caller learns the `expected` and the `got` so it can re-resume from the
    /// cursor. The node's chain is dense + monotone, so any other arrival order is
    /// a stream defect or an injection.
    OutOfOrder { expected: u64, got: u64 },
    /// The receipt's body does not hash to its claimed `receipt_hash` — a FORGED
    /// frame (the `receipt` was tampered, or the hash was swapped). Caught by
    /// recomputing the canonical `TurnReceipt::receipt_hash()` and comparing. This
    /// is the anti-ghost tooth: a surface NEVER reflects an unverified receipt.
    Forged {
        /// The position the forged frame claimed.
        chain_index: u64,
    },
    /// The claimed `receipt_hash` is not 32 hex-encoded bytes — a malformed frame
    /// (treated as a forge: it cannot be a genuine receipt commitment).
    MalformedHash { chain_index: u64 },
}

impl core::fmt::Display for IngestError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            IngestError::OutOfOrder { expected, got } => {
                write!(f, "out-of-order receipt: expected chain_index {expected}, got {got}")
            }
            IngestError::Forged { chain_index } => write!(
                f,
                "forged receipt at chain_index {chain_index}: body does not hash to claimed receipt_hash"
            ),
            IngestError::MalformedHash { chain_index } => {
                write!(f, "malformed receipt_hash at chain_index {chain_index}: not 32 hex bytes")
            }
        }
    }
}

impl std::error::Error for IngestError {}

/// The outcome of a single [`ReceiptStream::ingest`] of a well-formed, in-order,
/// un-forged frame.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Admitted {
    /// The receipt was NEW (the expected next dense position) and is now delivered.
    New,
    /// The receipt was a benign at-least-once RE-DELIVERY of an already-delivered
    /// position (a reconnect replayed it) — verified again, deduplicated, the
    /// cursor unchanged. Not an error: the node is at-least-once across reconnects.
    Duplicate,
}

/// **The live receipt-stream subscription.** Feed it the SSE frames a node's
/// `GET /api/events/stream` serves (parsed into [`ReceiptEnvelope`]s) via
/// [`ReceiptStream::ingest`]; it verifies each (in-order + un-forged), advances the
/// resume [`Cursor`], and retains a bounded tail of [`StreamedReceipt`]s a surface
/// reflects. The pure verification core is always available; the async `Stream`
/// edge (the `stream` feature) lets the cockpit `.await` it.
pub struct ReceiptStream {
    /// The verified receipts retained, newest LAST, bounded to `cap`.
    delivered: VecDeque<StreamedReceipt>,
    /// Max retained receipts (a live feed is unbounded; a surface shows a tail).
    cap: usize,
    /// The resume cursor — the highest chain index delivered, or [`Cursor::ORIGIN`]
    /// before anything. Drives both `next_expected()` and `Last-Event-ID` resume.
    cursor: Cursor,
    /// Receipts admitted-but-not-yet-`.await`-drained, oldest first — the queue the
    /// `Stream` impl (and `next_ready`) yields from. A surface that only reads
    /// `since`/`delivered` can ignore this; the async edge drains it.
    ready: VecDeque<StreamedReceipt>,
}

impl ReceiptStream {
    /// A fresh subscription tailing from genesis, retaining the last `cap` verified
    /// receipts (e.g. 256 for an inspector tail). The first receipt it expects is
    /// `chain_index == 0`.
    pub fn new(cap: usize) -> Self {
        Self::resuming(cap, Cursor::ORIGIN)
    }

    /// A subscription RESUMING from `cursor` (a reconnect): the first receipt it
    /// expects is `cursor.next_expected()`, and a re-delivery at/below the cursor
    /// is deduplicated. The retained tail starts empty (the surface keeps its own
    /// rendered history; this is the live edge).
    pub fn resuming(cap: usize, cursor: Cursor) -> Self {
        ReceiptStream {
            delivered: VecDeque::new(),
            cap: cap.max(1),
            cursor,
            ready: VecDeque::new(),
        }
    }

    /// **Ingest one streamed receipt frame.** The two gates, in order:
    ///
    /// 1. **Forge-check (always, FIRST).** Recompute the canonical
    ///    `receipt.receipt_hash()` and compare to the frame's claimed `receipt_hash`.
    ///    A mismatch is [`IngestError::Forged`]; a non-hex claim is
    ///    [`IngestError::MalformedHash`]. A forged frame is refused REGARDLESS of its
    ///    position — a surface never reflects an unverified body.
    /// 2. **Order-check.** If the (verified) `chain_index` is the expected next
    ///    dense position, it is [`Admitted::New`] (delivered, cursor advances). If it
    ///    is exactly the LAST delivered position re-arriving, it is
    ///    [`Admitted::Duplicate`] (a benign reconnect replay, deduplicated). Any
    ///    other index — a gap, or a deeper rewind — is [`IngestError::OutOfOrder`].
    ///
    /// On [`Admitted::New`] the receipt joins both the retained tail and the
    /// `.await`-able ready queue.
    pub fn ingest(&mut self, env: ReceiptEnvelope) -> Result<Admitted, IngestError> {
        let chain_index = env.row.chain_index;

        // ── Gate 1: forge-check. Recompute the canonical digest from the body. ──
        let recomputed = env.receipt.receipt_hash();
        let claimed = env
            .claimed_hash_bytes()
            .ok_or(IngestError::MalformedHash { chain_index })?;
        if recomputed != claimed {
            return Err(IngestError::Forged { chain_index });
        }

        // ── Gate 2: order-check against the dense cursor. ──
        let expected = self.cursor.next_expected();
        if chain_index == expected {
            // The next dense position — admit + advance.
            let sr = StreamedReceipt {
                proof_status: env.proof_status,
                chain_index,
                receipt_hash: recomputed,
                height: env.row.height,
                cells: env.row.cells,
                kinds: env.row.kinds,
                receipt: env.receipt,
            };
            self.cursor = Cursor::delivered_through(chain_index);
            if self.delivered.len() == self.cap {
                self.delivered.pop_front();
            }
            self.delivered.push_back(sr.clone());
            self.ready.push_back(sr);
            Ok(Admitted::New)
        } else if self.cursor != Cursor::ORIGIN && chain_index == self.cursor.0 {
            // A benign at-least-once re-delivery of the immediate last position
            // (a reconnect replayed `Last-Event-ID`). Verified (above), dedup'd.
            Ok(Admitted::Duplicate)
        } else {
            // A gap (skipped a dense entry) or a deeper rewind — a stream defect /
            // injection. The node's chain is dense + monotone; nothing else is valid.
            Err(IngestError::OutOfOrder {
                expected,
                got: chain_index,
            })
        }
    }

    /// The resume [`Cursor`] — the `Last-Event-ID` the next connection replays. A
    /// reconnecting reader passes `resume_cursor().last_event_id()` as the header so
    /// the node resumes from the next dense entry (lossless, idempotent).
    pub fn resume_cursor(&self) -> Cursor {
        self.cursor
    }

    /// The verified retained tail, newest LAST — what a surface reflects.
    pub fn delivered(&self) -> impl Iterator<Item = &StreamedReceipt> {
        self.delivered.iter()
    }

    /// The verified receipts STRICTLY AFTER `cursor` (the `Dynamics::since`
    /// analogue): a surface stores its last-seen cursor and replays only what is
    /// NEW. Yields every delivered receipt whose `chain_index > cursor.0` — i.e.
    /// everything past what the cursor has already seen — newest last. At
    /// [`Cursor::ORIGIN`] (nothing seen yet) it yields the whole retained tail.
    pub fn since(&self, cursor: Cursor) -> impl Iterator<Item = &StreamedReceipt> {
        let after = cursor.last_event_id(); // None at origin → all
        self.delivered
            .iter()
            .filter(move |r| after.map(|a| r.chain_index > a).unwrap_or(true))
    }

    /// The most recent verified receipt, if any (what an inspector focuses by
    /// default).
    pub fn latest(&self) -> Option<&StreamedReceipt> {
        self.delivered.back()
    }

    /// How many verified receipts are retained in the tail.
    pub fn len(&self) -> usize {
        self.delivered.len()
    }

    /// Whether the retained tail is empty.
    pub fn is_empty(&self) -> bool {
        self.delivered.is_empty()
    }

    /// Pull the next admitted-but-undrained receipt, oldest first (the pure pull
    /// the async `Stream` edge wraps). `None` when the ready queue is drained — the
    /// caller (a frame loop, or `poll_next`) waits for the next `ingest`. A surface
    /// that reads `since`/`delivered` directly need not call this.
    pub fn next_ready(&mut self) -> Option<StreamedReceipt> {
        self.ready.pop_front()
    }

    /// How many admitted receipts await draining via [`next_ready`] /
    /// `poll_next` — the cockpit's `cx.notify()` budget.
    pub fn pending(&self) -> usize {
        self.ready.len()
    }

    /// **Verify the whole delivered prefix against a federation's
    /// [`dregg_types::AttestedRoot`].** A subscriber that holds the federation's
    /// signed attested root for the period the delivered receipts fall in can prove
    /// the stream it was served is the one the federation committed: recompute the
    /// receipt-stream Merkle root over the delivered receipts' canonical hashes (in
    /// the dense `chain_index` order they were delivered — the federation's commit
    /// order) and check it equals the root's bound `receipt_stream_root`.
    ///
    /// This is the REAL [`AttestedRoot::verify_receipt_stream`] — the Silver-Vision
    /// "the WitnessedReceipt chain IS the persistence layer" binding. Returns
    /// `false` for a v3-legacy root (no `receipt_stream_root`) or any divergence.
    ///
    /// NB: this verifies the *full delivered set* maps to the root. It is the
    /// stream-level analogue of the per-frame forge-check: gate 1 catches a single
    /// tampered body locally (no root needed); this catches a federation that served
    /// a divergent stream, third-party-checkably.
    pub fn verify_against(&self, root: &AttestedRoot) -> bool {
        let hashes: Vec<[u8; 32]> = self.delivered.iter().map(|r| r.receipt_hash).collect();
        root.verify_receipt_stream(&hashes)
    }

    /// The receipt-stream Merkle root over the delivered prefix (the value a
    /// federation's `receipt_stream_root` must equal). Exposed so a producer can
    /// compute the binding it will sign, and a test can assert the round-trip
    /// without an `AttestedRoot`.
    pub fn delivered_stream_root(&self) -> [u8; 32] {
        let hashes: Vec<[u8; 32]> = self.delivered.iter().map(|r| r.receipt_hash).collect();
        merkle_root_of_receipt_hashes(&hashes)
    }
}

// ── hex helpers (no new dep: this crate already names `dregg_types::hex_encode`'s
//    family; we keep a local lowercase encoder + a strict 32-byte decoder so the
//    primitive carries no `hex` crate of its own — the same minimalism the rest of
//    the crate keeps). ──

/// Lowercase-hex-encode bytes (the node's `receipt_hash` wire convention).
fn encode_hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push(char::from_digit((b >> 4) as u32, 16).unwrap());
        s.push(char::from_digit((b & 0x0f) as u32, 16).unwrap());
    }
    s
}

/// Strictly decode exactly 32 hex bytes (64 hex chars) — `None` otherwise. A
/// receipt commitment is always 32 bytes, so a frame that is not is malformed.
fn decode_hex32(s: &str) -> Option<[u8; 32]> {
    let s = s.trim();
    if s.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    let bytes = s.as_bytes();
    for i in 0..32 {
        let hi = (bytes[2 * i] as char).to_digit(16)?;
        let lo = (bytes[2 * i + 1] as char).to_digit(16)?;
        out[i] = ((hi << 4) | lo) as u8;
    }
    Some(out)
}

// ───────────────────────────────────────────────────────────────────────────────
// The async `Stream` edge (the cockpit-async seam) — gated behind `stream`.
// ───────────────────────────────────────────────────────────────────────────────

/// A [`futures_core::Stream`] over a [`ReceiptStream`]'s ready queue — the edge the
/// cockpit's gpui async executor `.await`s. `poll_next` yields each admitted
/// [`StreamedReceipt`] (oldest first); when the ready queue is drained it returns
/// `Poll::Pending` after registering the waker, and a later [`ReceiptStream`]-feeding
/// task wakes it.
///
/// This wrapper deliberately holds the [`ReceiptStream`] by `&mut`-able ownership
/// behind the poll; the byte-pull/wake plumbing (a channel from the SSE reader
/// thread, the waker stored on feed) is the cockpit-wiring follow-on named at the
/// foot of this module — here we provide the SHAPE the executor drives, fed
/// synchronously, so the contract (`poll_next` yields verified receipts in order)
/// is testable without a runtime.
#[cfg(feature = "stream")]
pub struct ReceiptStreamPoll<'a> {
    inner: &'a mut ReceiptStream,
}

#[cfg(feature = "stream")]
impl<'a> ReceiptStreamPoll<'a> {
    /// Wrap a [`ReceiptStream`] as a pollable stream over its ready queue.
    pub fn new(inner: &'a mut ReceiptStream) -> Self {
        ReceiptStreamPoll { inner }
    }
}

#[cfg(feature = "stream")]
impl futures_core::Stream for ReceiptStreamPoll<'_> {
    type Item = StreamedReceipt;

    fn poll_next(
        mut self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Option<Self::Item>> {
        match self.inner.next_ready() {
            Some(sr) => std::task::Poll::Ready(Some(sr)),
            None => {
                // Drained: the cockpit's feeding task wakes us on the next `ingest`.
                // We register the waker so a runtime knows to re-poll. (The wiring
                // that STORES + calls this waker on feed is the named follow-on.)
                cx.waker().wake_by_ref();
                std::task::Poll::Pending
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Build a real `TurnReceipt` whose canonical `receipt_hash()` is meaningful —
    /// the fields the digest binds (turn_hash, agent, timestamp, computrons, ...)
    /// are seeded distinctly by `seed` so distinct receipts have distinct hashes.
    fn receipt(seed: u8) -> TurnReceipt {
        let mut agent = [0u8; 32];
        agent[0] = 0xA0;
        agent[1] = seed;
        TurnReceipt {
            turn_hash: [seed; 32],
            forest_hash: [seed.wrapping_add(1); 32],
            pre_state_hash: [seed.wrapping_add(2); 32],
            post_state_hash: [seed.wrapping_add(3); 32],
            effects_hash: [seed.wrapping_add(4); 32],
            timestamp: 1_718_000_000 + seed as i64,
            computrons_used: 100 + seed as u64,
            action_count: 1 + seed as usize,
            agent: dregg_types::CellId::derive_raw(&agent, &[0u8; 32]),
            ..Default::default()
        }
    }

    /// An HONEST frame at `idx` carrying `receipt(seed)`.
    fn frame(idx: u64, seed: u8) -> ReceiptEnvelope {
        ReceiptEnvelope::honest(idx, 1880 + idx, receipt(seed))
    }

    #[test]
    fn coordination_policy_survives_ingest_without_changing_receipt_identity() {
        let mut envelope = frame(0, 7);
        let hash = envelope.receipt.receipt_hash();
        envelope.proof_status = Some("not_required".into());
        let mut stream = ReceiptStream::new(4);
        assert_eq!(stream.ingest(envelope).unwrap(), Admitted::New);
        let row = stream.next_ready().unwrap();
        assert_eq!(row.proof_status.as_deref(), Some("not_required"));
        assert_eq!(row.receipt_hash, hash);
    }

    // ── Guarantee 1: a subscriber sees committed receipts IN ORDER. ──

    #[test]
    fn a_subscriber_sees_committed_receipts_in_order() {
        let mut s = ReceiptStream::new(64);
        for idx in 0..5u64 {
            assert_eq!(s.ingest(frame(idx, idx as u8)).unwrap(), Admitted::New);
        }
        // The delivered tail is exactly 0..5 in dense order, newest last.
        let got: Vec<u64> = s.delivered().map(|r| r.chain_index).collect();
        assert_eq!(got, vec![0, 1, 2, 3, 4]);
        assert_eq!(s.latest().unwrap().chain_index, 4);
        assert_eq!(s.resume_cursor(), Cursor::delivered_through(4));
        // Every delivered receipt's hash is the RECOMPUTED canonical one (verified).
        for r in s.delivered() {
            assert_eq!(r.receipt_hash, r.receipt.receipt_hash());
        }
    }

    #[test]
    fn the_ready_queue_yields_admitted_receipts_oldest_first() {
        let mut s = ReceiptStream::new(64);
        for idx in 0..3u64 {
            s.ingest(frame(idx, idx as u8)).unwrap();
        }
        assert_eq!(s.pending(), 3);
        assert_eq!(s.next_ready().unwrap().chain_index, 0);
        assert_eq!(s.next_ready().unwrap().chain_index, 1);
        assert_eq!(s.next_ready().unwrap().chain_index, 2);
        assert!(s.next_ready().is_none());
        assert_eq!(s.pending(), 0);
    }

    // ── Guarantee 2: a cursor RESUMES (lossless, idempotent). ──

    #[test]
    fn a_cursor_resumes_after_a_reconnect() {
        // Deliver 0,1,2; the cursor is 2; a fresh stream RESUMES from it.
        let mut s = ReceiptStream::new(64);
        for idx in 0..3u64 {
            s.ingest(frame(idx, idx as u8)).unwrap();
        }
        let cur = s.resume_cursor();
        assert_eq!(cur.last_event_id(), Some(2)); // the `Last-Event-ID` to replay

        // The reconnect: a NEW stream resuming from cursor 2. The node re-delivers
        // 2 (at-least-once) then a fresh 3 — 2 dedups, 3 is new.
        let mut s2 = ReceiptStream::resuming(64, cur);
        assert_eq!(s2.ingest(frame(2, 2)).unwrap(), Admitted::Duplicate); // replayed
        assert_eq!(s2.ingest(frame(3, 3)).unwrap(), Admitted::New); // fresh
        assert_eq!(s2.resume_cursor(), Cursor::delivered_through(3));
        // Only the genuinely-new receipt is in the resumed tail.
        let got: Vec<u64> = s2.delivered().map(|r| r.chain_index).collect();
        assert_eq!(got, vec![3]);
    }

    #[test]
    fn since_returns_only_what_is_new_past_a_cursor() {
        let mut s = ReceiptStream::new(64);
        for idx in 0..5u64 {
            s.ingest(frame(idx, idx as u8)).unwrap();
        }
        // A surface that last saw through chain index 2 replays only 3,4.
        let seen = Cursor::delivered_through(2);
        let fresh: Vec<u64> = s.since(seen).map(|r| r.chain_index).collect();
        assert_eq!(fresh, vec![3, 4]);
        // From origin, `since` yields the whole tail.
        let all: Vec<u64> = s.since(Cursor::ORIGIN).map(|r| r.chain_index).collect();
        assert_eq!(all, vec![0, 1, 2, 3, 4]);
    }

    // ── Guarantee 3: an out-of-order / FORGED item is REJECTED. ──

    #[test]
    fn an_out_of_order_receipt_is_rejected() {
        let mut s = ReceiptStream::new(64);
        s.ingest(frame(0, 0)).unwrap();
        // A GAP: chain_index 2 when 1 was expected → OutOfOrder, nothing delivered.
        let gap = s.ingest(frame(2, 2));
        assert_eq!(
            gap,
            Err(IngestError::OutOfOrder {
                expected: 1,
                got: 2
            })
        );
        assert_eq!(s.len(), 1, "the gapped receipt was NOT delivered");
        assert_eq!(
            s.resume_cursor(),
            Cursor::delivered_through(0),
            "cursor un-advanced"
        );
        // The correct next index still flows after the rejection.
        assert_eq!(s.ingest(frame(1, 1)).unwrap(), Admitted::New);

        // A deeper REWIND (an index below the immediate-last, not a benign dup) →
        // OutOfOrder too. Deliver up to 2, then replay 0.
        s.ingest(frame(2, 2)).unwrap();
        let rewind = s.ingest(frame(0, 0));
        assert_eq!(
            rewind,
            Err(IngestError::OutOfOrder {
                expected: 3,
                got: 0
            })
        );
    }

    #[test]
    fn a_forged_receipt_is_rejected() {
        let mut s = ReceiptStream::new(64);
        s.ingest(frame(0, 0)).unwrap();

        // A FORGED frame: claim index 1, but the claimed receipt_hash does NOT match
        // the body (the hash of a DIFFERENT receipt) — the body was swapped / the
        // hash was lied about. Caught by recomputing the canonical digest.
        let honest_hash = encode_hex(&receipt(99).receipt_hash());
        let forged = ReceiptEnvelope::new(
            1,
            honest_hash, // claims to be receipt(99)...
            1881,
            vec![],
            vec![],
            receipt(7), // ...but the BODY is receipt(7). Mismatch.
        );
        assert_eq!(
            s.ingest(forged),
            Err(IngestError::Forged { chain_index: 1 })
        );
        assert_eq!(s.len(), 1, "the forged receipt was NOT delivered");
        assert_eq!(
            s.resume_cursor(),
            Cursor::delivered_through(0),
            "cursor un-advanced"
        );

        // The forge-check fires REGARDLESS of position (even at a would-be-valid
        // index): a surface never reflects an unverified body. The honest receipt(1)
        // at index 1 still flows.
        assert_eq!(s.ingest(frame(1, 1)).unwrap(), Admitted::New);
    }

    #[test]
    fn a_tampered_body_under_a_real_hash_is_rejected() {
        // The sharper forge: take an HONEST frame and mutate the body AFTER the
        // claimed hash was set (a malicious relay rewriting the receipt). The
        // recomputed digest diverges → Forged.
        let mut s = ReceiptStream::new(64);
        let mut env = frame(0, 0); // honest: claimed hash == receipt(0).receipt_hash()
        env.receipt.computrons_used += 1; // tamper the body; hash now stale
        assert_eq!(s.ingest(env), Err(IngestError::Forged { chain_index: 0 }));
        assert!(s.is_empty());
    }

    #[test]
    fn a_malformed_hash_is_rejected() {
        let mut s = ReceiptStream::new(64);
        let env = ReceiptEnvelope::new(0, "not-hex".into(), 1880, vec![], vec![], receipt(0));
        assert_eq!(
            s.ingest(env),
            Err(IngestError::MalformedHash { chain_index: 0 })
        );
        assert!(s.is_empty());
    }

    // ── The frame deserializes from the genuine SSE `data:` JSON. ──

    #[test]
    fn an_envelope_deserializes_from_the_sse_data_payload() {
        // The SSE `data:` payload is `events::ReceiptEvent` serialized; our envelope
        // reads the row fields (flattened) + the full `receipt`. Round-trip a real
        // receipt through serde_json to prove the wire shape lines up.
        let r = receipt(5);
        let claimed = encode_hex(&r.receipt_hash());
        let json = serde_json::json!({
            "chain_index": 5u64,
            "receipt_hash": claimed,
            "turn_hash": encode_hex(&r.turn_hash), // wire carries it; we ignore it
            "height": 1885u64,
            "cells": [encode_hex(r.agent.as_bytes())],
            "kinds": ["transfer"],
            "has_proof": true,           // wire carries it; not load-bearing here
            "finality": "final",
            "timestamp": r.timestamp,
            "receipt": r,                // the full canonical receipt
        });
        let env: ReceiptEnvelope = serde_json::from_value(json).expect("envelope decodes");
        assert_eq!(env.row.chain_index, 5);
        assert_eq!(env.row.kinds, vec!["transfer".to_string()]);
        // And it ingests as a verified, in-order receipt.
        let mut s = ReceiptStream::resuming(64, Cursor::delivered_through(4));
        assert_eq!(s.ingest(env).unwrap(), Admitted::New);
        assert_eq!(s.latest().unwrap().chain_index, 5);
    }

    // ── The attested-root cross-check (the stream-level Silver binding). ──

    #[test]
    fn the_delivered_prefix_verifies_against_an_attested_root() {
        use dregg_types::AttestedRoot;
        let mut s = ReceiptStream::new(64);
        for idx in 0..4u64 {
            s.ingest(frame(idx, idx as u8)).unwrap();
        }
        // The federation's attested root binds the receipt-stream root over the SAME
        // delivered receipts in commit (dense) order.
        let bound = s.delivered_stream_root();
        let mut root = AttestedRoot::new_legacy([0u8; 32], 4, 0, vec![], None, 0);
        root.receipt_stream_root = Some(bound);
        assert!(
            s.verify_against(&root),
            "the delivered stream matches the attested root"
        );

        // A root binding a DIFFERENT stream (one extra receipt) does NOT verify.
        let mut s2 = ReceiptStream::new(64);
        for idx in 0..5u64 {
            s2.ingest(frame(idx, idx as u8)).unwrap();
        }
        let other = s2.delivered_stream_root();
        let mut root_other = AttestedRoot::new_legacy([0u8; 32], 5, 0, vec![], None, 0);
        root_other.receipt_stream_root = Some(other);
        assert!(
            !s.verify_against(&root_other),
            "a divergent stream is rejected by the root"
        );

        // A v3-legacy root (no receipt_stream_root) never verifies (fail-closed).
        let legacy = AttestedRoot::new_legacy([0u8; 32], 4, 0, vec![], None, 0);
        assert!(
            !s.verify_against(&legacy),
            "a v3 root without the binding fails closed"
        );
    }

    // ── The async `Stream` edge yields verified receipts in order. ──

    #[cfg(feature = "stream")]
    #[test]
    fn the_stream_edge_polls_verified_receipts_in_order() {
        use futures_core::Stream;
        use std::pin::Pin;
        use std::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};

        // A no-op waker so we can poll synchronously (the real waker is the cockpit's).
        fn noop_waker() -> Waker {
            fn no_op(_: *const ()) {}
            fn clone(_: *const ()) -> RawWaker {
                RawWaker::new(std::ptr::null(), &VTABLE)
            }
            static VTABLE: RawWakerVTable = RawWakerVTable::new(clone, no_op, no_op, no_op);
            unsafe { Waker::from_raw(RawWaker::new(std::ptr::null(), &VTABLE)) }
        }

        let mut s = ReceiptStream::new(64);
        for idx in 0..3u64 {
            s.ingest(frame(idx, idx as u8)).unwrap();
        }

        let waker = noop_waker();
        let mut cx = Context::from_waker(&waker);
        let mut poll = ReceiptStreamPoll::new(&mut s);
        // poll_next yields 0,1,2 in order, then Pending (queue drained).
        for expected in 0..3u64 {
            match Pin::new(&mut poll).poll_next(&mut cx) {
                Poll::Ready(Some(sr)) => assert_eq!(sr.chain_index, expected),
                other => panic!("expected receipt #{expected}, got {other:?}"),
            }
        }
        assert!(matches!(
            Pin::new(&mut poll).poll_next(&mut cx),
            Poll::Pending
        ));
    }
}
