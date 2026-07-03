//! **THE MATRIX ROOM** — membrane-over-Matrix, landed in the shipped desktop.
//!
//! The comms organ already proved every piece of the star feature in isolation:
//! `deos-matrix` owns the wire vocabulary (a [`MembraneEnvelope`] riding a normal
//! `m.room.message`, live-proved against a real homeserver AND against the
//! recorded/mock sync), and `starbridge-v2` owns the REAL executor legs (the
//! frustum mint / fail-closed rehydrate / receipted drive / settlement-gated
//! stitch of [`crate::shared_fork::MembraneFrustum`], plus the world-backed chat
//! discipline of [`crate::world_chat`]). What no surface did was put them in the
//! SHIPPED desktop. This window is that weld:
//!
//!   * **A room IS a cell.** Opening the window installs one live cell per wire
//!     room onto the desktop's OWN [`World`] ledger (the same census the icons
//!     read), plus the operator's Matrix-hand principal holding real caps to each.
//!   * **A send IS a receipted turn.** The composer commits a genuine
//!     `SetField` turn through `World::commit_turn` — the same conservation /
//!     ocap / program gates as every other transition, a real `TurnReceipt` in
//!     the Transcript, THE PULSE announcing it. No shadow chat store exists:
//!     the live timeline is decoded back OFF the recorded receipt chain
//!     ([`World::recorded_turns`]), never from a side table.
//!   * **An envelope IS the wire shape.** "⬡ mint membrane" forks the LIVE
//!     World, culls the real frustum around the Matrix-hand, wraps it in the
//!     exact [`MembraneEnvelope`] the Matrix event carries, round-trips it
//!     through the event JSON (the leg `client::tests` wire-proved), and posts
//!     it through the sync backend. "▶ rehydrate & drive" opens the envelope
//!     fail-closed (anti-substitution root tooth), commits a REAL verified turn
//!     on the rehydrated fork, and folds the genuine diff back through the
//!     branch-and-stitch settlement gate — conflicts surfaced, never silently
//!     dropped.
//!   * **The sync backend is the recorded sync** — [`deos_matrix::MockSource`],
//!     the same offline backend the deos-matrix suite live-proved. Its seeded
//!     membrane (a wire-shape stand-in with a mock root) is deliberately kept:
//!     driving it through the REAL executor REFUSES fail-closed, on the glass —
//!     the honest difference between a wire shape and an executor-real payload.
//!
//! ## The named seam: the live homeserver
//!
//! The federated leg (a logged-in [`deos_matrix::worker::MatrixHandle`] doing
//! real syncs) is NOT taken tonight. It is a *named, env-gated seam*:
//! [`HomeserverSeam`] reads [`HOMESERVER_URL_ENV`] / [`HOMESERVER_USER_ENV`] and
//! the Wire face shows its status honestly ("unset — riding the recorded
//! sync"). The wire types, the send path, and the envelope legs here are the
//! SAME ones `MatrixHandle` implements ([`deos_matrix::ChatSource`]), so taking
//! the seam is a backend swap, not a rewrite. (Mind the `libsqlite3-sys`
//! `links` constraint documented in `starbridge-v2/Cargo.toml` before wiring
//! the on-disk store.)
//!
//! ## The clobber-safe split
//!
//! Mirrors [`super::agent_room`] + [`super::app_shelf`]: a gpui-free model (the
//! sentinel, the tab vocabulary, the pure field codec, the [`MatrixRoomStack`]
//! and its envelope operations — all `cargo test`-able headless) plus an
//! `impl DeosDesktop` view half (the house pattern) owning the listeners, the
//! composer `InputState`, and the NT window body. The codec, tabs, and seam are
//! unconditional; everything touching `deos_matrix` wire types is gated on
//! `dev-surfaces` (where that dep lives), and a build without it falls back to
//! the inspector body exactly like the other gated windows.

use dregg_cell::FieldElement;
use dregg_types::CellId;

// ── The sentinel ──────────────────────────────────────────────────────────────────

/// The deterministic anchor cell the desktop hosts the Matrix Room window under —
/// a distinct non-ledger sentinel (like the Agent Room's `0xA6` and the
/// bot-surface's `0xB0`) so the room opens as its OWN window keyed apart from any
/// inspectable cell.
pub fn matrix_room_window_cell() -> CellId {
    CellId::from_bytes([0xFEu8; 32]) // 'FEderation'
}

/// Whether `cell` keys the Matrix Room window (drives the pane title + body).
pub fn is_matrix_room(cell: &CellId) -> bool {
    cell == &matrix_room_window_cell()
}

// ── The faces ─────────────────────────────────────────────────────────────────────

/// The faces of the Matrix Room — the moldable multiplicity over one room.
#[derive(Clone, Copy, Default, PartialEq, Eq)]
pub enum MatrixRoomTab {
    /// The merged timeline: the wire's recorded history + the LIVE leg (every
    /// message decoded off the World's receipt chain, receipt hash on the row).
    #[default]
    Timeline,
    /// The membrane envelopes riding this room — mint / rehydrate & drive /
    /// stitch, each leg the REAL executor.
    Envelopes,
    /// The sync backend + the named live-homeserver seam, shown honestly.
    Wire,
}

impl MatrixRoomTab {
    /// The tab caption the caller draws on the clickable strip.
    pub fn label(self) -> &'static str {
        match self {
            MatrixRoomTab::Timeline => "Timeline",
            MatrixRoomTab::Envelopes => "Envelopes",
            MatrixRoomTab::Wire => "Wire",
        }
    }

    /// Every tab, in display order — the caller iterates this to build the strip.
    pub const ALL: [MatrixRoomTab; 3] = [
        MatrixRoomTab::Timeline,
        MatrixRoomTab::Envelopes,
        MatrixRoomTab::Wire,
    ];
}

/// The per-window view state of a Matrix Room — which room is watched and which
/// face is shown. The caller holds this keyed by the window's sentinel cell.
#[derive(Clone, Default)]
pub struct MatrixRoomState {
    /// Index into the stack's room census (0 = the first wire room).
    pub room: usize,
    pub tab: MatrixRoomTab,
}

// ── The field codec (pure, fail-closed) ─────────────────────────────────────────────
//
// The SAME 32-byte-slot discipline `crate::world_chat` proved, adapted to the
// receipt-chain read: a message is ONE verified turn whose `SetField` effects
// write `field[0]` = header (`MAGIC ‖ len(8) ‖ sender-tag(16)`) and
// `field[1..=15]` = the UTF-8 body, 32 bytes per slot. The timeline decodes each
// recorded turn's effects back into `(sender, body)` — the chat has NO store of
// its own; the chronicle IS the timeline.

/// The header marker distinguishing a chat turn's `field[0]` write from any other
/// `SetField` on the room cell (a non-chat write decodes to `None`, fail-closed).
pub const CHAT_MAGIC: u8 = 0xDC;
/// Body slots per message (`field[1..=15]`).
pub const BODY_SLOTS: usize = 15;
/// Max message bytes (`15 × 32 = 480` — ample for chat).
pub const MAX_BODY: usize = BODY_SLOTS * 32;

/// Derive a stable 16-byte sender tag from a user id (the on-turn author marker;
/// the display id is recovered by reverse lookup, never a second truth).
pub fn sender_tag(user_id: &str) -> [u8; 16] {
    let h = blake3::hash(user_id.as_bytes());
    let mut t = [0u8; 16];
    t.copy_from_slice(&h.as_bytes()[..16]);
    t
}

/// Pack one message into `(field index, value)` writes — the effect payload of
/// the send turn. `None` when the body exceeds [`MAX_BODY`] (refused before any
/// turn is built, fail-closed).
pub fn pack_message(tag: [u8; 16], body: &str) -> Option<Vec<(usize, FieldElement)>> {
    let bytes = body.as_bytes();
    if bytes.len() > MAX_BODY {
        return None;
    }
    let mut header = [0u8; 32];
    header[0] = CHAT_MAGIC;
    header[1..9].copy_from_slice(&(bytes.len() as u64).to_le_bytes());
    header[9..25].copy_from_slice(&tag);
    let mut writes = Vec::with_capacity(1 + bytes.len().div_ceil(32));
    writes.push((0usize, header));
    for (i, chunk) in bytes.chunks(32).enumerate() {
        let mut f = [0u8; 32];
        f[..chunk.len()].copy_from_slice(chunk);
        writes.push((1 + i, f));
    }
    Some(writes)
}

/// Decode one recorded turn's `SetField` writes back into `(sender tag, body)`.
/// `None` for anything that is not a well-formed chat turn (wrong magic, absurd
/// length, non-UTF-8) — the decode is fail-closed, so a stray `SetField` on the
/// room cell can never fabricate a message.
pub fn decode_message(writes: &[(usize, FieldElement)]) -> Option<([u8; 16], String)> {
    let header = writes.iter().find(|(i, _)| *i == 0).map(|(_, v)| v)?;
    if header[0] != CHAT_MAGIC {
        return None;
    }
    let len = u64::from_le_bytes(header[1..9].try_into().ok()?) as usize;
    if len > MAX_BODY {
        return None;
    }
    let mut tag = [0u8; 16];
    tag.copy_from_slice(&header[9..25]);
    let mut bytes = Vec::with_capacity(len);
    for slot in 1..=BODY_SLOTS {
        if bytes.len() >= len {
            break;
        }
        let Some((_, v)) = writes.iter().find(|(i, _)| *i == slot) else {
            return None; // a hole in the body — not a chat turn's shape
        };
        let take = (len - bytes.len()).min(32);
        bytes.extend_from_slice(&v[..take]);
    }
    if bytes.len() != len {
        return None;
    }
    let body = String::from_utf8(bytes).ok()?;
    Some((tag, body))
}

// ── The named live-homeserver seam (env-gated config) ──────────────────────────────

/// The env var naming the live homeserver, `HOMESERVER_URL` style. Unset = the
/// window rides the recorded sync (tonight's honest scope).
pub const HOMESERVER_URL_ENV: &str = "DEOS_HOMESERVER_URL";
/// The env var naming the Matrix user id for the live leg (`@user:server`).
pub const HOMESERVER_USER_ENV: &str = "DEOS_HOMESERVER_USER";

/// **The live-homeserver leg, as configuration** — the named seam. Tonight the
/// desktop reads it and SHOWS it (the Wire face), and the recorded sync remains
/// the backend either way; the follow-up that takes the seam builds a logged-in
/// `MatrixHandle` from exactly these two values (it already implements the same
/// `ChatSource` the stack drives, so the swap is one constructor).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HomeserverSeam {
    pub url: Option<String>,
    pub user: Option<String>,
}

impl HomeserverSeam {
    /// Build the seam from explicit parts (the pure, testable constructor).
    pub fn from_parts(url: Option<String>, user: Option<String>) -> Self {
        let clean = |s: Option<String>| s.filter(|v| !v.trim().is_empty());
        HomeserverSeam {
            url: clean(url),
            user: clean(user),
        }
    }

    /// Whether the operator configured the live leg (both halves present).
    pub fn configured(&self) -> bool {
        self.url.is_some() && self.user.is_some()
    }

    /// The honest one-line status the Wire face shows.
    pub fn status_line(&self) -> String {
        match (&self.url, &self.user) {
            (Some(url), Some(user)) => {
                format!("configured — {user} @ {url} (leg not yet taken; recorded sync active)")
            }
            (Some(url), None) => {
                format!("{url} set but {HOMESERVER_USER_ENV} unset — riding the recorded sync")
            }
            _ => format!("{HOMESERVER_URL_ENV} unset — riding the recorded sync"),
        }
    }
}

/// Read the seam off the environment (the desktop's entry; tests use
/// [`HomeserverSeam::from_parts`]).
pub fn homeserver_seam() -> HomeserverSeam {
    HomeserverSeam::from_parts(
        std::env::var(HOMESERVER_URL_ENV).ok(),
        std::env::var(HOMESERVER_USER_ENV).ok(),
    )
}

/// Hex of the first 4 bytes (the 8-char prefix every dense face uses). Only the
/// `dev-surfaces` half renders ids, so the lean build carries it silently.
#[cfg_attr(not(feature = "dev-surfaces"), allow(dead_code))]
fn hex8(bytes: &[u8]) -> String {
    use std::fmt::Write as _;
    let mut s = String::with_capacity(8);
    for b in bytes.iter().take(4) {
        let _ = write!(s, "{b:02x}");
    }
    s
}

// ═══════════════════════════════════════════════════════════════════════════════════
// The dev-surfaces half — everything that touches the deos-matrix wire types.
// ═══════════════════════════════════════════════════════════════════════════════════

#[cfg(feature = "dev-surfaces")]
mod stack {
    use super::*;
    use std::collections::{HashMap, HashSet};

    use deos_matrix::membrane::{FrustumCut, MembraneEnvelope, WitnessCursor};
    use deos_matrix::source::{ChatSource, MockSource};

    use dregg_cell::AuthRequired;

    use crate::branch_stitch::{BranchCap, SettleOutcome, Stitch};
    use crate::replay::RecordedStep;
    use crate::shared_fork::MembraneFrustum;
    use crate::world::{open_permissions, set_field, World};

    /// How many capability hops the membrane cull follows from the Matrix-hand
    /// (the frustum's far plane): the hand + every room cell it reaches.
    pub const MEMBRANE_DEPTH: u8 = 2;

    /// One live room: the wire room's identity plus its REAL cell on the
    /// desktop's World ledger (room = cell, the deos-matrix discipline).
    pub struct RoomSpec {
        /// The room's live cell on `World::ledger()` (the icon, the inspector,
        /// and every send turn's target).
        pub cell: CellId,
        /// The Matrix room id (`!room:server`) — the wire key.
        pub matrix_id: String,
        pub name: String,
        pub topic: String,
    }

    /// Which leg a timeline row rode in on.
    #[derive(Clone, Copy, PartialEq, Eq)]
    pub enum Leg {
        /// The recorded sync (the wire's history — no executor claim made).
        Wire,
        /// The LIVE leg: decoded off the World's receipt chain, receipt on the row.
        Live,
    }

    /// One merged timeline row (wire history first, then the live leg — the
    /// recorded past under the receipted present).
    pub struct TimelineRow {
        pub leg: Leg,
        pub sender: String,
        pub body: String,
        /// Live leg: `receipt <hex8> · turn #<n>` — the executor's proof line.
        pub receipt: Option<String>,
        /// Set when this row carries a membrane envelope (the Envelopes face
        /// drives it by this wire event id).
        pub membrane_event: Option<String>,
    }

    /// One envelope card on the Envelopes face.
    pub struct EnvelopeRow {
        /// The wire event id the envelope rode in (the drive key).
        pub event_id: String,
        pub sender: String,
        /// Minted from THIS desktop's live World this session (vs arrived on the
        /// wire's recorded history).
        pub minted_live: bool,
        pub envelope: MembraneEnvelope,
        /// The last drive verdict on this card (settled / REFUSED …), if any.
        pub verdict: Option<String>,
    }

    /// The witness of one send that committed (the composer's return).
    pub struct SentTurn {
        pub height: u64,
        pub receipt_hex: String,
    }

    /// The granular outcome of one rehydrate → drive → stitch pass — every claim
    /// a checker can re-verify (no self-reported "done").
    #[derive(Debug)]
    pub struct DriveOutcome {
        /// Cells the rehydrated fork holds (== the envelope's declared cull).
        pub fork_cells: usize,
        /// The fork's state root AFTER the driven verified turn.
        pub post_root: [u8; 32],
        /// Atoms the settlement gate folded clean.
        pub folded: usize,
        /// Whether the gate refused an over-authorized confer (the lossy-drop).
        pub over_authorized: bool,
    }

    impl DriveOutcome {
        /// The one-line verdict the card + status bar show.
        pub fn summary(&self) -> String {
            if self.over_authorized {
                format!(
                    "over-authorized confer refused (lossy-drop) · fork of {} cell(s) drove to {}…",
                    self.fork_cells,
                    hex8(&self.post_root)
                )
            } else {
                format!(
                    "settled — {} atom(s) folded clean · fork of {} cell(s) drove to {}…",
                    self.folded,
                    self.fork_cells,
                    hex8(&self.post_root)
                )
            }
        }
    }

    /// **The Matrix Room's whole substance** — the live room cells + the
    /// Matrix-hand principal on the desktop's World, the recorded-sync wire, and
    /// the envelope ledger (event id → drive verdict). Owned by `DeosDesktop`;
    /// gpui-free, so every leg is `cargo test`-able headless.
    pub struct MatrixRoomStack {
        pub rooms: Vec<RoomSpec>,
        /// The operator's Matrix-hand principal — a real cell holding caps to
        /// every room cell (its turns are what the ocap gate ADMITS).
        pub me_cell: CellId,
        /// The operator's Matrix display id (the wire's `whoami`).
        pub me: String,
        /// The sync backend: the recorded/mock sync deos-matrix live-proved.
        wire: MockSource,
        /// Sender tag → display id (reverse lookup of the on-turn tag).
        senders: HashMap<[u8; 16], String>,
        /// Wire event ids of envelopes minted from THIS live World this session.
        minted: HashSet<String>,
        /// Per-envelope drive verdicts (event id → the last summary), view-state.
        verdicts: HashMap<String, String>,
    }

    impl MatrixRoomStack {
        /// **Install the Matrix Room onto the LIVE World** — one open cell per
        /// wire room + the Matrix-hand principal holding caps to each (grafted
        /// BEFORE its install, the `world_chat` discipline: a later send is a
        /// pure receipted `SetField` turn the ocap gate legitimately admits).
        /// Cell ids derive from the room's Matrix id, so they are stable and
        /// collision-free against the demo census.
        pub fn install_on_world(world: &mut World) -> MatrixRoomStack {
            let wire = MockSource::seeded();
            let me = wire
                .whoami()
                .unwrap_or_else(|| "@ember:deos.local".to_string());

            let mut rooms = Vec::new();
            for summary in wire.rooms().unwrap_or_default() {
                let matrix_id = summary.room_id.to_string();
                // A deterministic, domain-separated pk per room (the cell id
                // derives from it) — no collision with seed-byte fixture cells.
                let mut hasher = blake3::Hasher::new();
                hasher.update(b"deos-desktop-matrix-room-v1");
                hasher.update(matrix_id.as_bytes());
                let pk = *hasher.finalize().as_bytes();
                let mut cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], 0);
                cell.permissions = open_permissions();
                let id = world.genesis_install(cell);
                rooms.push(RoomSpec {
                    cell: id,
                    matrix_id,
                    name: summary.display_name.clone(),
                    topic: summary.topic.clone().unwrap_or_default(),
                });
            }

            // The Matrix-hand principal, installed LAST holding caps to every
            // room cell (grafted pre-install — no genesis-after-turn mutation).
            let mut hasher = blake3::Hasher::new();
            hasher.update(b"deos-desktop-matrix-hand-v1");
            hasher.update(me.as_bytes());
            let pk = *hasher.finalize().as_bytes();
            let mut hand = dregg_cell::Cell::with_balance(pk, [0u8; 32], 0);
            hand.permissions = open_permissions();
            for r in &rooms {
                hand.capabilities.grant(r.cell, AuthRequired::None);
            }
            let me_cell = world.genesis_install(hand);

            let mut senders = HashMap::new();
            senders.insert(sender_tag(&me), me.clone());
            MatrixRoomStack {
                rooms,
                me_cell,
                me,
                wire,
                senders,
                minted: HashSet::new(),
                verdicts: HashMap::new(),
            }
        }

        /// The wire backend's honest label (the recorded sync says "mock").
        pub fn wire_backend(&self) -> &'static str {
            self.wire.backend_label()
        }

        /// **SEND = a real receipted turn.** Pack the body into `SetField`
        /// effects on the room's live cell and commit them as ONE verified turn
        /// by the Matrix-hand — the same gates every transition runs through.
        /// Fail-closed on an over-long body and on an executor refusal.
        pub fn send(&self, world: &mut World, room: usize, body: &str) -> Result<SentTurn, String> {
            let spec = self.rooms.get(room).ok_or("no such room")?;
            let writes = pack_message(sender_tag(&self.me), body)
                .ok_or_else(|| format!("message too long ({} > {MAX_BODY} bytes)", body.len()))?;
            let effects = writes
                .into_iter()
                .map(|(i, v)| set_field(spec.cell, i, v))
                .collect();
            let turn = world.turn(self.me_cell, effects);
            let outcome = world.commit_turn(turn);
            if !outcome.is_committed() {
                return Err(format!(
                    "the send turn was refused by the executor (fail-closed): {outcome:?}"
                ));
            }
            let receipt_hex = world
                .receipts()
                .last()
                .map(|r| hex8(&r.receipt_hash()))
                .unwrap_or_else(|| "????????".to_string());
            Ok(SentTurn {
                height: world.height(),
                receipt_hex,
            })
        }

        /// **The LIVE timeline — decoded off the receipt chain.** Walk the
        /// World's recorded history and reverse every committed chat turn on
        /// this room's cell back into `(sender, body)`, receipt hash attached.
        /// There is no message store to drift from the ledger: this read IS the
        /// ledger's chronicle. (Chat sends are single-root turns, so root
        /// actions are the whole shape walked here.)
        pub fn live_timeline(&self, world: &World, room: usize) -> Vec<(String, String, String)> {
            let Some(spec) = self.rooms.get(room) else {
                return Vec::new();
            };
            let mut out = Vec::new();
            let mut committed = 0u64;
            for step in world.recorded_turns().steps() {
                let RecordedStep::Committed { turn, receipt, .. } = step else {
                    continue;
                };
                committed += 1;
                let mut writes: Vec<(usize, FieldElement)> = Vec::new();
                for root in &turn.call_forest.roots {
                    for eff in &root.action.effects {
                        if let dregg_turn::action::Effect::SetField { cell, index, value } = eff {
                            if *cell == spec.cell {
                                writes.push((*index, *value));
                            }
                        }
                    }
                }
                if let Some((tag, body)) = decode_message(&writes) {
                    let sender = self
                        .senders
                        .get(&tag)
                        .cloned()
                        .unwrap_or_else(|| "@unknown:deos.local".to_string());
                    out.push((
                        sender,
                        body,
                        format!(
                            "receipt {} · turn #{committed}",
                            hex8(&receipt.receipt_hash())
                        ),
                    ));
                }
            }
            out
        }

        /// The merged timeline: the wire's recorded history first (the past),
        /// then the LIVE leg (the receipted present) — every row labeled by leg.
        pub fn timeline_rows(&self, world: &World, room: usize) -> Vec<TimelineRow> {
            let mut rows = Vec::new();
            if let Some(spec) = self.rooms.get(room) {
                for m in self.wire.timeline(&spec.matrix_id, 80).unwrap_or_default() {
                    rows.push(TimelineRow {
                        leg: Leg::Wire,
                        sender: m.sender.clone(),
                        body: m.body.clone(),
                        receipt: None,
                        membrane_event: m.membrane.is_some().then(|| m.event_id.clone()),
                    });
                }
            }
            for (sender, body, receipt) in self.live_timeline(world, room) {
                rows.push(TimelineRow {
                    leg: Leg::Live,
                    sender,
                    body,
                    receipt: Some(receipt),
                    membrane_event: None,
                });
            }
            rows
        }

        /// **Mint a membrane of the LIVE World and post it through the wire.**
        /// Forks the live World (the screenshot of the moment), culls the REAL
        /// frustum around the Matrix-hand ([`MembraneFrustum::mint`] — the hand
        /// + every room cell its caps reach, nothing beyond: confinement by
        /// omission), wraps it in the wire envelope, round-trips it through the
        /// Matrix event JSON (the `m.room.message` leg, fail-closed if mangled),
        /// and sends it through the sync backend. Returns the wire event id.
        pub fn mint_and_post(&mut self, world: &World, room: usize) -> Result<String, String> {
            let spec = self.rooms.get(room).ok_or("no such room")?;
            let env = mint_envelope(world, self.me_cell, MEMBRANE_DEPTH);

            // THE MATRIX EVENT LEG: the envelope must survive the JSON wire
            // byte-faithfully (the shape client::tests wire-proved live).
            let json =
                serde_json::to_string(&env).map_err(|e| format!("envelope serialize: {e}"))?;
            let back: MembraneEnvelope =
                serde_json::from_str(&json).map_err(|e| format!("envelope deserialize: {e}"))?;
            if back != env {
                return Err("the event JSON mangled the envelope (fail-closed)".into());
            }

            let event_id = self
                .wire
                .send_membrane(&spec.matrix_id, "", back)
                .map_err(|e| e.to_string())?;
            self.minted.insert(event_id.clone());
            Ok(event_id)
        }

        /// The envelope cards riding this room, read back off the WIRE timeline
        /// each call (live truth — no shadow list to drift).
        pub fn envelopes(&self, room: usize) -> Vec<EnvelopeRow> {
            let Some(spec) = self.rooms.get(room) else {
                return Vec::new();
            };
            self.wire
                .timeline(&spec.matrix_id, 80)
                .unwrap_or_default()
                .into_iter()
                .filter_map(|m| {
                    let env = m.membrane?;
                    Some(EnvelopeRow {
                        minted_live: self.minted.contains(&m.event_id),
                        verdict: self.verdicts.get(&m.event_id).cloned(),
                        event_id: m.event_id,
                        sender: m.sender,
                        envelope: env,
                    })
                })
                .collect()
        }

        /// **Rehydrate & drive one envelope card** — the REAL executor pass over
        /// whatever the wire delivered. Stores + returns the verdict line: green
        /// for a settled fold, the fail-closed refusal (root mismatch /
        /// malformed snapshot / newer version) for anything the executor will
        /// not trust — including the recorded sync's own mock-root sample.
        pub fn drive_card(&mut self, room: usize, event_id: &str) -> String {
            let Some(row) = self
                .envelopes(room)
                .into_iter()
                .find(|r| r.event_id == event_id)
            else {
                return "no such envelope on this room's wire".to_string();
            };
            let verdict = match rehydrate_drive_stitch(&row.envelope) {
                Ok(outcome) => outcome.summary(),
                Err(e) => format!("REFUSED (fail-closed) — {e}"),
            };
            self.verdicts.insert(event_id.to_string(), verdict.clone());
            verdict
        }
    }

    /// **Mint the wire envelope from a fork of the live World** — the real
    /// frustum ([`MembraneFrustum`], genuine `Cell`s, the blake3 root the
    /// rehydrate tooth re-derives) wrapped in the exact `MembraneEnvelope` the
    /// Matrix message carries. Mirrors `comms_pd_source::mint_membrane`.
    pub fn mint_envelope(world: &World, focus: CellId, depth: u8) -> MembraneEnvelope {
        let fork = world.fork();
        let frustum = MembraneFrustum::mint(&fork, focus, depth);
        let root = frustum.frustum_root();
        let snapshot = frustum.to_snapshot_bytes();
        MembraneEnvelope {
            version: MembraneEnvelope::VERSION,
            frustum_root: root,
            sturdyref: format!("dregg://fork/{}", hex8(&root)),
            lineage: focus.as_bytes().to_vec(),
            snapshot,
            cut: FrustumCut {
                focus_cell: *focus.as_bytes(),
                max_depth: depth,
                authority_bounded: true,
                cell_count: frustum.cells.len() as u32,
            },
            cursor: WitnessCursor {
                height: frustum.minted_height,
                commit_index: 0,
            },
        }
    }

    /// **Rehydrate a received envelope, drive a REAL verified turn on the fork,
    /// and stitch the genuine diff back through the settlement gate.** Every
    /// tooth fail-closed: a newer wire version, a malformed snapshot, or a
    /// substituted root is refused before a single cell is trusted. Mirrors
    /// `comms_pd_source::rehydrate_drive_stitch`, returning the granular
    /// [`DriveOutcome`] a checker can re-verify.
    pub fn rehydrate_drive_stitch(env: &MembraneEnvelope) -> Result<DriveOutcome, String> {
        // (1) Forward-compat + anti-substitution, fail-closed.
        if !env.is_rehydratable() {
            return Err(
                "membrane wire version is newer than this build — refusing (fail-closed)".into(),
            );
        }
        let frustum =
            MembraneFrustum::from_snapshot_bytes(&env.snapshot).map_err(|e| e.to_string())?;
        let mut fork = frustum
            .rehydrate(env.frustum_root)
            .map_err(|e| e.to_string())?;
        let fork_cells = fork.ledger().iter().count();

        // (2) DRIVE a real verified turn on the rehydrated fork: the focus cell
        //     if present (the cell in view), else the first — a genuine mutation
        //     committed through the fork's verified executor.
        let focus = CellId::from_bytes(env.cut.focus_cell);
        let target = if fork.ledger().get(&focus).is_some() {
            focus
        } else {
            match fork.ledger().iter().next() {
                Some((id, _)) => *id,
                None => return Err("rehydrated fork is empty — nothing to drive".into()),
            }
        };
        let drive = fork.turn(
            target,
            vec![crate::world::set_field(target, 0, [0xD7u8; 32])],
        );
        if !fork.commit_turn(drive).is_committed() {
            return Err("the driven turn was refused by the fork executor (fail-closed)".into());
        }

        // (3) STITCH the REAL driven diff back through the settlement gate: the
        //     clean part folds (LUB); an over-authorized confer is a transparent
        //     lossy-drop, never a silent overwrite.
        let (baseline, driven) = frustum.driven_graphs(&fork);
        fn cell_key(id: &CellId) -> u64 {
            let b = id.as_bytes();
            u64::from_le_bytes([b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]])
        }
        let conferred: Vec<BranchCap> = frustum
            .cells
            .iter()
            .map(|c| BranchCap {
                target: cell_key(&c.id()),
                debit_reach: false,
            })
            .collect();
        let stitch = Stitch {
            main: baseline,
            branch: driven,
            conferred: conferred.clone(),
        };
        match stitch.settle(&conferred, None) {
            SettleOutcome::Settled(merged) => Ok(DriveOutcome {
                fork_cells,
                post_root: fork.state_root(),
                folded: merged.atoms.len(),
                over_authorized: false,
            }),
            SettleOutcome::Refused { .. } => Ok(DriveOutcome {
                fork_cells,
                post_root: fork.state_root(),
                folded: 0,
                over_authorized: true,
            }),
        }
    }

    // ── The bake witness (shared by the bake hook + the tests) ──────────────────────

    /// The witnesses of one full membrane-over-Matrix round trip on the live
    /// World — every boolean re-derived from a real operation, none asserted.
    pub struct MembraneRoundtrip {
        /// Cells the minted frustum culled (the hand + its capability reach).
        pub minted_cells: u32,
        /// The wire event id the envelope rode in (the Matrix event leg).
        pub wire_event: String,
        /// The envelope read BACK off the wire rehydrated fail-closed into a
        /// real fork (the anti-substitution root reproduced).
        pub rehydrated: bool,
        /// One REAL verified turn committed on the rehydrated fork.
        pub drove: bool,
        /// Atoms the settlement gate folded clean on the stitch back.
        pub folded: usize,
        /// A root-tampered copy of the same envelope was REFUSED.
        pub tamper_refused: bool,
        /// The recorded sync's seeded mock-root envelope was REFUSED by the
        /// real executor (the wire shape is not the executor's trust).
        pub wire_sample_refused: bool,
        /// The verdict line the card shows.
        pub summary: String,
    }

    /// Run the full round trip: mint off the LIVE World → the event-JSON wire →
    /// read back → rehydrate → drive → stitch, plus the two refusal probes
    /// (tampered root; the wire's own mock sample). The bake hook and the test
    /// suite both call THIS, so the desktop proves what the tests prove.
    pub fn membrane_roundtrip(
        world: &World,
        stack: &mut MatrixRoomStack,
        room: usize,
    ) -> Result<MembraneRoundtrip, String> {
        let wire_event = stack.mint_and_post(world, room)?;
        let row = stack
            .envelopes(room)
            .into_iter()
            .find(|r| r.event_id == wire_event)
            .ok_or("the posted envelope did not come back off the wire")?;
        let env = row.envelope;

        let outcome = rehydrate_drive_stitch(&env)?;
        let summary = outcome.summary();
        stack.verdicts.insert(wire_event.clone(), summary.clone());

        // Refusal probe 1: substitute the claimed root — must fail closed.
        let mut tampered = env.clone();
        tampered.frustum_root[0] ^= 0xff;
        let tamper_refused = rehydrate_drive_stitch(&tampered).is_err();

        // Refusal probe 2: the recorded sync's seeded sample (a wire-shape
        // stand-in with a mock root) — the REAL executor must refuse it.
        let wire_sample_refused = stack
            .envelopes(room)
            .into_iter()
            .find(|r| !r.minted_live)
            .map(|r| rehydrate_drive_stitch(&r.envelope).is_err())
            .unwrap_or(true); // no sample on this room = nothing to mistrust

        Ok(MembraneRoundtrip {
            minted_cells: env.cut.cell_count,
            wire_event,
            rehydrated: outcome.fork_cells as u32 == env.cut.cell_count,
            drove: true, // rehydrate_drive_stitch errors when the drive refuses
            folded: outcome.folded,
            tamper_refused,
            wire_sample_refused,
            summary,
        })
    }
}

#[cfg(feature = "dev-surfaces")]
pub use stack::{
    membrane_roundtrip, mint_envelope, rehydrate_drive_stitch, DriveOutcome, EnvelopeRow, Leg,
    MatrixRoomStack, MembraneRoundtrip, RoomSpec, SentTurn, TimelineRow, MEMBRANE_DEPTH,
};

// ═══════════════════════════════════════════════════════════════════════════════════
// The View half — the house pattern (`app_shelf`/`halo`): an `impl DeosDesktop`
// block owning the listeners, the composer InputState, and the NT window body.
// ═══════════════════════════════════════════════════════════════════════════════════

#[cfg(feature = "dev-surfaces")]
mod view {
    use super::*;

    use gpui::prelude::FluentBuilder as _;
    use gpui::{
        div, px, AnyElement, AppContext as _, Context, FontWeight, InteractiveElement, IntoElement,
        MouseButton, MouseDownEvent, ParentElement, ScrollHandle, Styled, Window,
    };
    use gpui_component::input::{Input, InputEvent, InputState};

    use super::super::chrome::{
        bevel_raised, face_row, face_row_color, face_section, id_hex, id_short, nt_scroll_face,
        NT_OK, NT_PANEL, NT_SELECT, NT_WARN,
    };
    use super::super::{DeosDesktop, FaceScrollKey, WinKindTag};

    // ── Pure face renderers (no listeners — the caller composes the strips) ────────

    /// The TIMELINE face — the wire's recorded history under the LIVE leg, every
    /// live row carrying the executor's receipt line. Pure presentation.
    fn render_timeline_body(rows: &[TimelineRow], scroll: &ScrollHandle) -> AnyElement {
        let live = rows.iter().filter(|r| r.leg == Leg::Live).count();
        let mut col = div()
            .id("matrix-timeline")
            .bg(gpui::rgb(0x101820))
            .text_color(gpui::rgb(0x9fe0a0))
            .p_2()
            .flex()
            .flex_col()
            .gap_1()
            .child(div().text_color(gpui::rgb(0x6fc0ff)).child(format!(
                "── {} message(s) · {live} on the LIVE leg (receipted turns) ",
                rows.len()
            )));
        if rows.is_empty() {
            return nt_scroll_face(scroll, col.child(div().child("(the room is quiet)")))
                .into_any_element();
        }
        for row in rows {
            let (badge, color) = match row.leg {
                Leg::Wire => ("⇅ wire", 0x8090a0u32),
                Leg::Live => ("⛓ live", 0x50e090u32),
            };
            let mut line = div()
                .flex()
                .flex_row()
                .gap_1()
                .text_size(px(11.0))
                .child(
                    div()
                        .w(px(48.0))
                        .text_color(gpui::rgb(color))
                        .font_weight(FontWeight::BOLD)
                        .child(badge),
                )
                .child(div().w(px(140.0)).child(row.sender.clone()))
                .child(div().flex_1().child(row.body.clone()));
            if let Some(receipt) = &row.receipt {
                line = line.child(div().text_color(gpui::rgb(0x6fc0ff)).child(receipt.clone()));
            }
            if row.membrane_event.is_some() {
                line = line.child(
                    div()
                        .text_color(gpui::rgb(0xffc060))
                        .child("⬡ envelope — drive it on the Envelopes face"),
                );
            }
            col = col.child(line);
        }
        nt_scroll_face(scroll, col).into_any_element()
    }

    /// The WIRE face — the sync backend + the named live-homeserver seam, shown
    /// honestly (the recorded sync is the backend; the env-gated seam is status,
    /// not a pretend connection). Pure presentation.
    fn render_wire_body(
        stack: &MatrixRoomStack,
        seam: &HomeserverSeam,
        scroll: &ScrollHandle,
    ) -> AnyElement {
        let mut col = div()
            .id("matrix-wire")
            .bg(gpui::rgb(NT_PANEL))
            .p_2()
            .flex()
            .flex_col()
            .gap_1()
            .child(face_section("The sync backend — what feeds this window"))
            .child(face_row(
                "backend",
                &format!(
                    "recorded sync (deos-matrix MockSource · label '{}')",
                    stack.wire_backend()
                ),
            ))
            .child(face_row("whoami", &stack.me))
            .child(face_row(
                "rooms",
                &format!("{} (each a live cell on this World)", stack.rooms.len()),
            ));
        for r in &stack.rooms {
            col = col.child(face_row(
                &r.name,
                &format!("{} · cell {} · {}", r.matrix_id, id_short(&r.cell), r.topic),
            ));
        }
        let (verdict, color) = if seam.configured() {
            (seam.status_line(), NT_OK)
        } else {
            (seam.status_line(), NT_WARN)
        };
        col = col
            .child(face_section(
                "The live-homeserver leg — a NAMED seam, env-gated",
            ))
            .child(face_row_color(HOMESERVER_URL_ENV, &verdict, color))
            .child(face_row(
                "when taken",
                "a logged-in MatrixHandle (the same ChatSource) replaces the recorded sync — \
                 one constructor, zero rewrites",
            ))
            .child(face_section("Fail-closed rules (the teeth)"))
            .child(face_row(
                "envelopes",
                "a substituted root / malformed snapshot / newer wire version is REFUSED \
                 before one cell is trusted",
            ))
            .child(face_row(
                "sends",
                "a refused turn is surfaced with the executor's reason — never faked committed",
            ));
        nt_scroll_face(scroll, col).into_any_element()
    }

    // ── The desktop half: actuation + the window body (the View owns listeners) ────

    impl DeosDesktop {
        /// Open (or focus) the MATRIX ROOM — installing the room cells + the
        /// Matrix-hand onto the LIVE World on first open (a census the icons
        /// immediately show), landed mold-ready like every global surface.
        pub(in crate::deos_desktop) fn open_matrix_room(&mut self) {
            self.ensure_matrix_stack();
            self.land_in(matrix_room_window_cell(), WinKindTag::MatrixRoom);
            let (rooms, me) = self
                .matrix_stack
                .as_ref()
                .map(|s| (s.rooms.len(), s.me.clone()))
                .unwrap_or((0, String::new()));
            self.say(format!(
                "Matrix Room — {rooms} room-cells on the LIVE World as {me}; every send a \
                 receipted turn, every envelope the real membrane wire shape."
            ));
        }

        /// Install the stack on first use: room cells + the Matrix-hand land on
        /// the live ledger, and the icon census refreshes so they stand on the
        /// desktop at once.
        fn ensure_matrix_stack(&mut self) {
            if self.matrix_stack.is_some() {
                return;
            }
            let stack = {
                let mut w = self.world.borrow_mut();
                MatrixRoomStack::install_on_world(&mut w)
            };
            // Re-read the icon census off the LIVE ledger (the same read
            // `DeosDesktop::new` makes) — the fresh cells appear immediately.
            let mut v: Vec<CellId> = {
                let w = self.world.borrow();
                w.ledger().iter().map(|(id, _)| *id).collect()
            };
            v.sort();
            self.cells = v;
            self.matrix_stack = Some(stack);
        }

        /// Build the composer's live input on first render — single-line, Enter
        /// commits the draft as a REAL receipted turn (the SAME send the bake
        /// hook drives). Mirrors the Spotter's input plumbing exactly.
        fn ensure_matrix_input(&mut self, window: &mut Window, cx: &mut Context<Self>) {
            if self.matrix_input.is_some() {
                return;
            }
            let input = cx.new(|cx| {
                InputState::new(window, cx)
                    .placeholder("Say it onto the World — Enter commits a receipted turn…")
            });
            let sub = cx.subscribe_in(
                &input,
                window,
                |this, input, ev: &InputEvent, window, cx| match ev {
                    InputEvent::Change => {
                        this.matrix_draft = input.read(cx).value().to_string();
                    }
                    InputEvent::PressEnter { .. } => {
                        this.matrix_send_draft();
                        input.update(cx, |st, cx| st.set_value("", window, cx));
                        cx.notify();
                    }
                    _ => {}
                },
            );
            self.matrix_input = Some(input);
            self.matrix_input_sub = Some(sub);
        }

        /// **SEND the composer draft** — one verified turn on the LIVE World; the
        /// verdict (receipt hash + height, or the executor's refusal) narrated.
        fn matrix_send_draft(&mut self) {
            let body = std::mem::take(&mut self.matrix_draft);
            let body = body.trim().to_string();
            if body.is_empty() {
                return;
            }
            let room = self
                .matrix_rooms
                .get(&matrix_room_window_cell())
                .map(|s| s.room)
                .unwrap_or(0);
            let outcome = {
                let mut w = self.world.borrow_mut();
                match self.matrix_stack.as_ref() {
                    Some(stack) => stack.send(&mut w, room, &body),
                    None => Err("the Matrix stack is not installed".into()),
                }
            };
            match outcome {
                Ok(sent) => self.say(format!(
                    "sent onto the World — receipt {} · height {} (the timeline reads it \
                     back off the chronicle).",
                    sent.receipt_hex, sent.height
                )),
                Err(e) => self.say(format!("send REFUSED: {e}")),
            }
        }

        /// **⬡ MINT a membrane of the live World** and post it through the wire —
        /// the whole envelope leg (fork → real frustum → event JSON → sync
        /// backend), narrated with the wire event id.
        fn matrix_mint_membrane(&mut self, room: usize) {
            let outcome = {
                let w = self.world.borrow();
                match self.matrix_stack.as_mut() {
                    Some(stack) => stack.mint_and_post(&w, room),
                    None => Err("the Matrix stack is not installed".into()),
                }
            };
            match outcome {
                Ok(event_id) => self.say(format!(
                    "membrane minted off the LIVE World and posted as {event_id} — a real \
                     frustum in the exact Matrix wire shape. Drive it on the Envelopes face."
                )),
                Err(e) => self.say(format!("mint REFUSED: {e}")),
            }
        }

        /// **▶ REHYDRATE & DRIVE one envelope card** — the real executor pass,
        /// verdict on the card + the status bar (settled fold, or the
        /// fail-closed refusal — including the wire's own mock sample).
        fn matrix_drive_card(&mut self, room: usize, event_id: &str) {
            let verdict = match self.matrix_stack.as_mut() {
                Some(stack) => stack.drive_card(room, event_id),
                None => "the Matrix stack is not installed".to_string(),
            };
            self.say(format!("rehydrate & drive {event_id}: {verdict}"));
        }

        /// **The Matrix Room window body** — the room picker strip + the face
        /// tabs + the selected face + (on Timeline) the live composer, all over
        /// the LIVE World each frame.
        pub(in crate::deos_desktop) fn render_matrix_room_window(
            &mut self,
            cell: CellId,
            window: &mut Window,
            cx: &mut Context<Self>,
        ) -> AnyElement {
            use MatrixRoomTab as T;
            self.ensure_matrix_stack();
            self.ensure_matrix_input(window, cx);
            let state = self.matrix_rooms.entry(cell).or_default().clone();
            // Each face keeps its OWN persistent scroll handle (tab ordinal keyed).
            let sc = self.face_scrolls.ensure(FaceScrollKey::Window(
                cell,
                WinKindTag::MatrixRoom,
                state.tab as u8,
            ));

            // The room picker — every wire room (each a live cell), the watched
            // one selected. Clicking pins the window to that room.
            let room_names: Vec<String> = self
                .matrix_stack
                .as_ref()
                .map(|s| s.rooms.iter().map(|r| r.name.clone()).collect())
                .unwrap_or_default();
            let mut picker = div().flex().flex_row().flex_wrap().gap_1().my_1();
            for (i, name) in room_names.iter().enumerate() {
                let selected = i == state.room;
                picker = picker.child(
                    bevel_raised(
                        div()
                            .id(gpui::SharedString::from(format!("mtx-room-{i}")))
                            .px_2()
                            .py_1()
                            .text_size(px(10.0))
                            .when_selected(selected),
                    )
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                            this.matrix_rooms.entry(cell).or_default().room = i;
                            cx.notify();
                        }),
                    )
                    .child(format!("#{name}")),
                );
            }

            // The face tabs — timeline / envelopes / wire.
            let mut tabs = div().flex().flex_row().gap_1().my_1();
            for t in T::ALL {
                let selected = t == state.tab;
                tabs = tabs.child(
                    bevel_raised(
                        div()
                            .id(gpui::SharedString::from(format!("mtx-tab-{}", t.label())))
                            .px_2()
                            .py_1()
                            .text_size(px(10.0))
                            .when_selected(selected),
                    )
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                            this.matrix_rooms.entry(cell).or_default().tab = t;
                            cx.notify();
                        }),
                    )
                    .child(t.label()),
                );
            }

            let body: AnyElement = match state.tab {
                T::Timeline => {
                    let world = self.world.borrow();
                    let rows = self
                        .matrix_stack
                        .as_ref()
                        .map(|s| s.timeline_rows(&world, state.room))
                        .unwrap_or_default();
                    drop(world);
                    render_timeline_body(&rows, &sc)
                }
                T::Envelopes => self.render_matrix_envelopes_face(state.room, &sc, cx),
                T::Wire => match self.matrix_stack.as_ref() {
                    Some(stack) => render_wire_body(stack, &homeserver_seam(), &sc),
                    None => div().child("(no stack)").into_any_element(),
                },
            };

            // The composer strip rides under the Timeline face only.
            let composer = (state.tab == T::Timeline).then(|| {
                let input = self.matrix_input.clone();
                div()
                    .flex()
                    .flex_row()
                    .gap_1()
                    .items_center()
                    .child(
                        div()
                            .flex_1()
                            .h(px(26.0))
                            .bg(gpui::rgb(0xffffff))
                            .when_some(input, |d, input| d.child(Input::new(&input).h_full())),
                    )
                    .child(
                        bevel_raised(
                            div()
                                .id("mtx-send")
                                .px_2()
                                .py_1()
                                .text_size(px(10.0))
                                .font_weight(FontWeight::BOLD),
                        )
                        .on_mouse_down(
                            MouseButton::Left,
                            cx.listener(|this, _ev: &MouseDownEvent, _w, cx| {
                                this.matrix_send_draft();
                                cx.notify();
                            }),
                        )
                        .child("Send ⛓"),
                    )
            });

            div()
                .id(gpui::SharedString::from(format!(
                    "mtxroom-body-{}",
                    id_hex(&cell)
                )))
                .flex_1()
                .min_h(px(0.0))
                .flex()
                .flex_col()
                .gap_1()
                .bg(gpui::rgb(NT_PANEL))
                .p_2()
                .child(picker)
                .child(tabs)
                .child(body)
                .children(composer)
                .into_any_element()
        }

        /// The ENVELOPES face — the mint affordance + every envelope card riding
        /// this room's wire, each with its "▶ rehydrate & drive" button and its
        /// last verdict (interactive, so it lives on the View half).
        fn render_matrix_envelopes_face(
            &mut self,
            room: usize,
            scroll: &ScrollHandle,
            cx: &mut Context<Self>,
        ) -> AnyElement {
            let rows = self
                .matrix_stack
                .as_ref()
                .map(|s| s.envelopes(room))
                .unwrap_or_default();

            let mut col = div()
                .id("matrix-envelopes")
                .bg(gpui::rgb(NT_PANEL))
                .p_2()
                .flex()
                .flex_col()
                .gap_1()
                .child(face_section(&format!(
                    "Envelopes · {} riding this room's wire",
                    rows.len()
                )))
                .child(
                    bevel_raised(
                        div()
                            .id("mtx-mint")
                            .px_2()
                            .py_1()
                            .text_size(px(10.0))
                            .font_weight(FontWeight::BOLD),
                    )
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                            this.matrix_mint_membrane(room);
                            cx.notify();
                        }),
                    )
                    .child("⬡ mint membrane of the LIVE World → post to this room"),
                );

            for row in rows {
                let origin = if row.minted_live {
                    ("minted HERE — a real frustum of this live World", NT_OK)
                } else {
                    ("arrived on the wire — trust only what rehydrates", NT_WARN)
                };
                let event_id = row.event_id.clone();
                let mut card = div()
                    .flex()
                    .flex_col()
                    .gap_1()
                    .p_1()
                    .bg(gpui::rgb(0x101820))
                    .text_color(gpui::rgb(0x9fe0a0))
                    .text_size(px(11.0))
                    .child(
                        div()
                            .text_color(gpui::rgb(0x6fc0ff))
                            .child(format!("⬡ {} · from {}", row.event_id, row.sender)),
                    )
                    .child(div().child(format!(
                        "root {}… · {} cell(s) · cut @h{} · v{}",
                        hex8(&row.envelope.frustum_root),
                        row.envelope.cut.cell_count,
                        row.envelope.cursor.height,
                        row.envelope.version
                    )))
                    .child(div().text_color(gpui::rgb(origin.1)).child(origin.0));
                if let Some(verdict) = &row.verdict {
                    let color = if verdict.starts_with("REFUSED") {
                        0xffc060
                    } else {
                        0x50e090
                    };
                    card = card.child(
                        div()
                            .text_color(gpui::rgb(color))
                            .child(format!("last drive: {verdict}")),
                    );
                }
                card = card.child(
                    bevel_raised(
                        div()
                            .id(gpui::SharedString::from(format!("mtx-drive-{event_id}")))
                            .px_2()
                            .py_1()
                            .text_size(px(10.0))
                            .font_weight(FontWeight::BOLD)
                            .text_color(gpui::rgb(0x000000)),
                    )
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                            this.matrix_drive_card(room, &event_id);
                            cx.notify();
                        }),
                    )
                    .child("▶ rehydrate & drive (real executor · fail-closed)"),
                );
                col = col.child(card);
            }
            nt_scroll_face(scroll, col).into_any_element()
        }

        // ── Bake / test hooks (drive the room headlessly) ─────────────────────────

        /// Open the Matrix Room window (what the desktop menu's entry does) —
        /// installs the stack on the live World on first call.
        pub fn bake_open_matrix_room(&mut self) {
            self.open_matrix_room();
        }

        /// SEND `body` to the currently-watched room as a real receipted turn
        /// (what the composer's Enter does). Returns whether the turn COMMITTED.
        pub fn bake_matrix_send(&mut self, body: &str) -> bool {
            self.ensure_matrix_stack();
            self.matrix_draft = body.to_string();
            let before = self.world.borrow().height();
            self.matrix_send_draft();
            self.world.borrow().height() > before
        }

        /// How many LIVE-leg messages the watched room's timeline decodes off
        /// the receipt chain (a bake assertion — the chronicle IS the timeline).
        pub fn bake_matrix_live_len(&mut self) -> usize {
            self.ensure_matrix_stack();
            let room = self
                .matrix_rooms
                .get(&matrix_room_window_cell())
                .map(|s| s.room)
                .unwrap_or(0);
            let world = self.world.borrow();
            self.matrix_stack
                .as_ref()
                .map(|s| s.live_timeline(&world, room).len())
                .unwrap_or(0)
        }

        /// **The full membrane round trip on the live desktop** — mint → event
        /// JSON → wire → rehydrate → drive → stitch, plus both refusal probes.
        /// The SAME witness path the unit tests assert on.
        pub fn bake_matrix_membrane_roundtrip(&mut self) -> Result<MembraneRoundtrip, String> {
            self.ensure_matrix_stack();
            let room = self
                .matrix_rooms
                .get(&matrix_room_window_cell())
                .map(|s| s.room)
                .unwrap_or(0);
            let world = self.world.borrow();
            match self.matrix_stack.as_mut() {
                Some(stack) => membrane_roundtrip(&world, stack, room),
                None => Err("the Matrix stack is not installed".into()),
            }
        }
    }

    /// A tiny local extension so the picker/tab chips read like the Agent Room's
    /// (selected = NT_SELECT face + white text) without repeating the closure.
    trait WhenSelected {
        fn when_selected(self, selected: bool) -> Self;
    }
    impl WhenSelected for gpui::Stateful<gpui::Div> {
        fn when_selected(self, selected: bool) -> Self {
            use gpui::prelude::FluentBuilder as _;
            self.when(selected, |d| {
                d.bg(gpui::rgb(NT_SELECT)).text_color(gpui::rgb(0xffffff))
            })
        }
    }
}

// ── Tests: the pure envelope model + the codec (headless, no renderer) ─────────────

#[cfg(test)]
mod tests {
    use super::*;

    // ── The codec (unconditional — compiles in every build) ──────────────────────

    #[test]
    fn the_field_codec_round_trips_a_message() {
        let tag = sender_tag("@ember:deos.local");
        let body = "hello membrane — the chat is the dregg world ✦";
        let writes = pack_message(tag, body).expect("packs");
        let (t, b) = decode_message(&writes).expect("decodes");
        assert_eq!(t, tag, "the sender tag survives the fields");
        assert_eq!(b, body, "the body survives the fields (unicode intact)");
    }

    #[test]
    fn the_codec_refuses_an_oversized_body_before_any_turn_exists() {
        let tag = sender_tag("@ember:deos.local");
        let too_long = "x".repeat(MAX_BODY + 1);
        assert!(pack_message(tag, &too_long).is_none(), "fail-closed pack");
        // And exactly-max packs (the boundary is inclusive).
        let max = "y".repeat(MAX_BODY);
        assert!(pack_message(tag, &max).is_some());
    }

    #[test]
    fn the_decode_is_fail_closed_against_non_chat_writes() {
        // A stray SetField(0, …) without the magic decodes to None — no
        // fabricated message can enter the timeline.
        let mut header = [0u8; 32];
        header[0] = 0x01; // not CHAT_MAGIC
        assert!(decode_message(&[(0, header)]).is_none());
        // A magic header claiming an absurd length is refused too.
        let mut lying = [0u8; 32];
        lying[0] = CHAT_MAGIC;
        lying[1..9].copy_from_slice(&(u64::MAX).to_le_bytes());
        assert!(decode_message(&[(0, lying)]).is_none());
        // A magic header whose body slots are missing (a hole) is refused.
        let tag = sender_tag("@x:y");
        let writes = pack_message(tag, "a body that spans two slots at least...").expect("packs");
        let holed: Vec<_> = writes.iter().filter(|(i, _)| *i != 1).cloned().collect();
        assert!(decode_message(&holed).is_none(), "a hole fails closed");
    }

    #[test]
    fn the_homeserver_seam_is_env_gated_config_not_a_connection() {
        let unset = HomeserverSeam::from_parts(None, None);
        assert!(!unset.configured());
        assert!(unset.status_line().contains("unset"));
        assert!(unset.status_line().contains("recorded sync"));

        let half = HomeserverSeam::from_parts(Some("https://m.ember.software".into()), None);
        assert!(!half.configured(), "half a config is not a config");

        let full = HomeserverSeam::from_parts(
            Some("https://m.ember.software".into()),
            Some("@ember:ember.software".into()),
        );
        assert!(full.configured());
        assert!(full.status_line().contains("configured"));
        assert!(
            full.status_line().contains("not yet taken"),
            "the seam names itself honestly even when configured"
        );

        // Whitespace-only values are unset (no accidental empty-string config).
        let blank = HomeserverSeam::from_parts(Some("  ".into()), Some("".into()));
        assert!(!blank.configured());
    }

    // ── The live legs (dev-surfaces — where the wire types live) ──────────────────

    #[cfg(feature = "dev-surfaces")]
    mod live {
        use super::super::*;
        use crate::world::demo_world;

        #[test]
        fn install_send_and_read_back_off_the_receipt_chain() {
            let (mut world, _anchors) = demo_world();
            let cells_before = world.cell_count();
            let stack = MatrixRoomStack::install_on_world(&mut world);
            assert_eq!(
                world.cell_count(),
                cells_before + stack.rooms.len() + 1,
                "one live cell per wire room + the Matrix-hand landed on the ledger"
            );
            assert!(!stack.rooms.is_empty(), "the wire census seeded rooms");

            // A fresh room decodes NO messages off the chain (fail-closed decode).
            assert!(stack.live_timeline(&world, 0).is_empty());

            // SEND = a real verified turn; the receipt is the world's own.
            let h_before = world.height();
            let body = "a receipted hello — over the membrane wire";
            let sent = stack.send(&mut world, 0, body).expect("send commits");
            assert_eq!(world.height(), h_before + 1, "one committed turn");
            let last = world.receipts().last().expect("a receipt landed");
            assert_eq!(
                sent.receipt_hex,
                {
                    let h = last.receipt_hash();
                    format!("{:02x}{:02x}{:02x}{:02x}", h[0], h[1], h[2], h[3])
                },
                "the send's receipt IS the world's last receipt"
            );

            // TIMELINE = decoded back off the recorded receipt chain, not a store.
            let tl = stack.live_timeline(&world, 0);
            assert_eq!(tl.len(), 1);
            assert_eq!(tl[0].1, body, "the body round-trips through the chronicle");
            assert_eq!(tl[0].0, stack.me, "the sender decodes from the on-turn tag");
            assert!(tl[0].2.contains(&sent.receipt_hex), "receipt on the row");

            // Ordering + isolation: a second send follows; other rooms are clean.
            stack.send(&mut world, 0, "second").expect("send 2");
            let tl2 = stack.live_timeline(&world, 0);
            assert_eq!(tl2.len(), 2);
            assert_eq!(tl2[0].1, body, "first stays first (chronicle order)");
            assert!(
                stack.live_timeline(&world, 1).is_empty(),
                "no cross-room leak"
            );

            // The merged rows carry the wire's recorded history UNDER the live leg.
            let rows = stack.timeline_rows(&world, 0);
            assert!(rows.iter().any(|r| r.leg == Leg::Wire));
            assert_eq!(rows.iter().filter(|r| r.leg == Leg::Live).count(), 2);

            // An oversized body is refused before any turn is built.
            let too_long = "z".repeat(MAX_BODY + 1);
            assert!(stack.send(&mut world, 0, &too_long).is_err());
            assert_eq!(world.height(), h_before + 2, "no turn escaped the refusal");
        }

        #[test]
        fn the_membrane_roundtrip_is_real_end_to_end_and_fail_closed() {
            let (mut world, _anchors) = demo_world();
            let mut stack = MatrixRoomStack::install_on_world(&mut world);

            let witness = membrane_roundtrip(&world, &mut stack, 0).expect("the round trip runs");
            assert!(
                witness.minted_cells as usize >= 1 + stack.rooms.len(),
                "the frustum culled the Matrix-hand + its whole capability reach"
            );
            assert!(
                witness.rehydrated,
                "the fork holds exactly the declared cull"
            );
            assert!(
                witness.drove,
                "one real verified turn committed on the fork"
            );
            assert!(
                witness.folded >= 1,
                "the stitch folded the driven mutation clean (got {})",
                witness.folded
            );
            assert!(witness.tamper_refused, "a substituted root is refused");
            assert!(
                witness.wire_sample_refused,
                "the recorded sync's mock-root sample is refused by the real executor"
            );
            assert!(witness.summary.contains("settled"), "{}", witness.summary);

            // The envelope card remembers its verdict (the face renders it).
            let card = stack
                .envelopes(0)
                .into_iter()
                .find(|r| r.event_id == witness.wire_event)
                .expect("the minted card rides the wire");
            assert!(card.minted_live);
            assert_eq!(card.verdict.as_deref(), Some(witness.summary.as_str()));
        }

        #[test]
        fn a_future_wire_version_is_refused_before_the_snapshot_is_touched() {
            let (mut world, _anchors) = demo_world();
            let stack = MatrixRoomStack::install_on_world(&mut world);
            let mut env = mint_envelope(&world, stack.me_cell, MEMBRANE_DEPTH);
            env.version += 1;
            let err = rehydrate_drive_stitch(&env).unwrap_err();
            assert!(
                err.contains("newer"),
                "fail-closed on forward-compat: {err}"
            );
        }

        #[test]
        fn the_envelope_survives_the_matrix_event_json_byte_faithfully() {
            let (mut world, _anchors) = demo_world();
            let stack = MatrixRoomStack::install_on_world(&mut world);
            let env = mint_envelope(&world, stack.me_cell, MEMBRANE_DEPTH);
            let json = serde_json::to_string(&env).expect("serializes");
            let back: deos_matrix::membrane::MembraneEnvelope =
                serde_json::from_str(&json).expect("deserializes");
            assert_eq!(back, env, "the wire is byte-faithful");
            // And what came back still rehydrates + drives + stitches for real.
            let outcome = rehydrate_drive_stitch(&back).expect("the real pass");
            assert_eq!(outcome.fork_cells as u32, env.cut.cell_count);
        }
    }
}
