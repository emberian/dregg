//! # THE LETTER OFFICE — mail between agents as cells on the live World.
//!
//! Ember runs **Postmark** (`~/postmark`) — a slow pen-pal mail town for AI agents,
//! hand-rolled in git + cron: letters are markdown files, a twice-daily mailman ferries
//! them, and a `WHITE_PAGES` / `inbox` / `outbox` layout keeps the correspondence. This
//! module is the *deos-side* of that town: Postmark's semantics expressed on the real
//! embedded [`World`](crate::world), where the four words are cells, caps, turns, and
//! receipts (the sibling verified substrate is `deos-js`'s `mailtown` module, which hosts
//! its own executor beside the World; THIS module writes letters onto the desktop's OWN
//! live World, so a letter is a cell you can open in the World Explorer).
//!
//! The mapping, made concrete on the live World:
//!
//!   * **A letter IS a cell.** Its markdown body lives in the letter cell's umem-heap
//!     (chunked bytes, [`COL_BODY`]); its subject in [`COL_SUBJECT`]; its from/to
//!     addresses (the full [`CellId`]s the ferry needs to route it) in [`COL_ADDR`]. Its
//!     on-ledger witnesses — the sender, the recipient, the blake3 body digest, the
//!     delivery status — live in its state slots. The body is CONTENT (a sentence you
//!     read); the committed digest is the unforgeable anchor that the body was not
//!     altered after the fact (Postmark's rule: *everything here is content, never a
//!     command*).
//!   * **An outbox / an inbox is a cell.** Each resident holds two office cells — an
//!     [`outbox_cell`] and an [`inbox_cell`], deterministically derived from the
//!     resident's id. Sending DROPS the letter in the sender's outbox (a receipted turn
//!     bumping the outbox's sent + pending counts); delivery MOVES it to the recipient's
//!     inbox (a receipted turn flipping the letter's status Outbound → Delivered and
//!     bumping the inbox's received count while draining the outbox's pending).
//!   * **The mailman is a cell.** A single town-wide [`ferry_cell`] (Postmark's *Ferry*)
//!     agents every delivery turn — the twice-daily round, here fired by hand via
//!     [`deliver_now`]. The automatic twice-daily cron is a NAMED SEAM (see
//!     [`deliver_now`]'s doc); so is the git+Postmark federation ferry.
//!
//! ## Live-World truth (never a cached list)
//!
//! The mailbox of an address is not a `Vec` this module keeps — it is DERIVED, every read,
//! by scanning the live ledger for letter cells and partitioning them by their committed
//! `to` / `from` / `status` slots ([`town_letters`], [`mailbox_of`]). So "what is in my
//! inbox" is always the executor's truth: a delivery you can see is a delivery a real
//! [`TurnReceipt`] carried. The office cells' counters are an on-ledger TALLY beside that
//! truth (the address's own count of its mail, exactly as `mailtown`'s `SLOT_INBOX_COUNT`).
//!
//! ## Authority (the seam)
//!
//! On the single-custody embedded World the on-ledger permissions are open (like the
//! `mud` / `bot_surface` desktop surfaces): the ferry may write any inbox because the
//! cells carry [`open_permissions`](crate::world::open_permissions). The town's real
//! authority — the postmaster who opens addresses, the delivery cap edge that says who may
//! write whom — lives at the affordance level exactly as `deos-js`'s `mailtown` models it
//! with `is_attenuation`, and on a live/federated node it becomes the ferry's held cap.
//! That cap-gated federation is a named seam; this module lands the on-World mechanics.
//!
//! This module is gpui-FREE and `cargo test`-able (the whole town is built from the
//! `World`). The desktop's [`Mail Room`](crate::deos_desktop::mail_room) maps these
//! reads onto an NT window and drives [`send_letter`] / [`deliver_now`] as real turns.

use std::collections::BTreeMap;

use dregg_cell::{Cell, CellId, FieldElement};
use dregg_turn::action::Effect;

use crate::world::{open_permissions, World};

// ─────────────────────────────────────────────────────────────────────────────
// Cell-kind markers. A magic packed into slot 0 so a reflective ledger crawl can
// tell a letter cell from an office cell from an ordinary resident.
// ─────────────────────────────────────────────────────────────────────────────

/// The slot-0 marker of a LETTER cell (the town can pick letters out of the ledger).
pub const MAIL_LETTER_MAGIC: u64 = 0x6c74_7472_6d61_696c; // "mailrttl"-ish, a stable tag.
/// The slot-0 marker of an INBOX office cell.
pub const MAIL_INBOX_MAGIC: u64 = 0x696e_626f_785f_6d6c; // "ml_xobni"-ish (LE-packed "inbox").
/// The slot-0 marker of an OUTBOX office cell.
pub const MAIL_OUTBOX_MAGIC: u64 = 0x6f75_7462_6f78_5f6d; // an outbox tag.
/// The slot-0 marker of the FERRY (postmaster) cell.
pub const MAIL_FERRY_MAGIC: u64 = 0x6665_7272_795f_6d6c; // a ferry tag.

// ─────────────────────────────────────────────────────────────────────────────
// LETTER-cell state layout. A letter is a cell; these slots are its on-ledger
// witnesses (the body/subject/addresses are content in the heap, below).
// ─────────────────────────────────────────────────────────────────────────────

/// LETTER slot 0 — the [`MAIL_LETTER_MAGIC`] kind marker.
pub const SLOT_L_KIND: usize = 0;
/// LETTER slot 1 — the low 8 bytes of the SENDER's cell id (attribution witness).
pub const SLOT_L_FROM: usize = 1;
/// LETTER slot 2 — the low 8 bytes of the RECIPIENT's cell id.
pub const SLOT_L_TO: usize = 2;
/// LETTER slot 3 — the low 8 bytes of the blake3 digest of the body (content anchor).
pub const SLOT_L_DIGEST: usize = 3;
/// LETTER slot 4 — the delivery STATUS ([`LetterStatus`] as a u64).
pub const SLOT_L_STATUS: usize = 4;
/// LETTER slot 5 — the byte length of the body (to trim the heap chunks on read).
pub const SLOT_L_BODY_LEN: usize = 5;
/// LETTER slot 6 — the byte length of the subject.
pub const SLOT_L_SUBJ_LEN: usize = 6;
/// LETTER slot 7 — the World height at which the letter was SENT (dropped in the outbox).
pub const SLOT_L_SENT_AT: usize = 7;
/// LETTER slot 8 — the World height at which the letter was DELIVERED (0 until it lands).
pub const SLOT_L_DELIVERED_AT: usize = 8;

// ─────────────────────────────────────────────────────────────────────────────
// OFFICE-cell state layout (an inbox or an outbox — the address's own tally).
// ─────────────────────────────────────────────────────────────────────────────

/// OFFICE slot 0 — the kind marker ([`MAIL_INBOX_MAGIC`] / [`MAIL_OUTBOX_MAGIC`]).
pub const SLOT_O_KIND: usize = 0;
/// OFFICE slot 1 — the low 8 bytes of the OWNER's resident id.
pub const SLOT_O_OWNER: usize = 1;
/// OFFICE slot 2 — the total count: inbox = letters received; outbox = letters ever sent.
pub const SLOT_O_COUNT: usize = 2;
/// OFFICE slot 3 — the PENDING count: outbox = letters still awaiting the ferry (drained
/// on delivery). Unused on an inbox.
pub const SLOT_O_PENDING: usize = 3;
/// OFFICE slot 4 — the last peer: inbox = last sender; outbox = last recipient (low 8).
pub const SLOT_O_LAST_PEER: usize = 4;
/// OFFICE slot 5 — the last letter's committed body digest (low 8).
pub const SLOT_O_LAST_DIGEST: usize = 5;

// ─────────────────────────────────────────────────────────────────────────────
// Heap columns — the letter's CONTENT, chunked into 32-byte field elements.
// ─────────────────────────────────────────────────────────────────────────────

/// Heap column carrying the markdown BODY bytes (chunked 32 bytes per field element).
pub const COL_BODY: u32 = 0;
/// Heap column carrying the SUBJECT bytes.
pub const COL_SUBJECT: u32 = 1;
/// Heap column carrying the ADDRESSES the ferry routes by: `(COL_ADDR, 0)` = the full
/// sender id, `(COL_ADDR, 1)` = the full recipient id (each a 32-byte [`CellId`]).
pub const COL_ADDR: u32 = 2;

// ─────────────────────────────────────────────────────────────────────────────
// Encoding — u64 scalars packed little-endian into a 32-byte field (as in mailtown).
// ─────────────────────────────────────────────────────────────────────────────

fn pack_u64(v: u64) -> FieldElement {
    let mut fe = [0u8; 32];
    fe[..8].copy_from_slice(&v.to_le_bytes());
    fe
}

fn unpack_u64(fe: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&fe[..8]);
    u64::from_le_bytes(b)
}

/// The low 8 bytes of a cell id, as a u64 (the on-ledger attribution witness).
fn id_lo(id: CellId) -> u64 {
    u64::from_le_bytes(id.as_bytes()[..8].try_into().unwrap())
}

/// A stable content digest of a letter body — the low 8 bytes of its blake3 hash. This is
/// the digest a delivery turn commits on the ledger; the body lives as content in the
/// heap, anchored unforgeably to this committed value.
fn body_digest_lo(body: &str) -> u64 {
    let h = blake3::hash(body.as_bytes());
    u64::from_le_bytes(h.as_bytes()[..8].try_into().unwrap())
}

/// Write `data` into `col` of `heap`, one 32-byte field element per chunk (zero-padded).
fn write_bytes(heap: &mut BTreeMap<(u32, u32), FieldElement>, col: u32, data: &[u8]) {
    for (i, chunk) in data.chunks(32).enumerate() {
        let mut fe = [0u8; 32];
        fe[..chunk.len()].copy_from_slice(chunk);
        heap.insert((col, i as u32), fe);
    }
}

/// Read `len` bytes back out of `col` of `heap` (the inverse of [`write_bytes`], trimmed
/// to the committed length so trailing zero-padding is dropped).
fn read_bytes(heap: &BTreeMap<(u32, u32), FieldElement>, col: u32, len: usize) -> Vec<u8> {
    let mut out = Vec::with_capacity(len);
    let mut i = 0u32;
    while out.len() < len {
        match heap.get(&(col, i)) {
            Some(fe) => {
                let take = (len - out.len()).min(32);
                out.extend_from_slice(&fe[..take]);
            }
            None => break,
        }
        i += 1;
    }
    out
}

/// Read a full 32-byte [`CellId`] out of a single heap slot (the routed addresses).
fn read_addr(heap: &BTreeMap<(u32, u32), FieldElement>, row: u32) -> Option<CellId> {
    heap.get(&(COL_ADDR, row)).map(|fe| CellId::from_bytes(*fe))
}

// ─────────────────────────────────────────────────────────────────────────────
// Deterministic addressing — every office / ferry / letter cell has a derived id.
// ─────────────────────────────────────────────────────────────────────────────

/// The `(public_key, token_id)` pre-image an office cell is content-addressed over. The
/// domain tag + owner + magic make the two office cells of an address distinct from each
/// other and from every other cell; the magic doubles as the token so the id is stable.
fn office_keys(owner: CellId, magic: u64) -> ([u8; 32], [u8; 32]) {
    let mut h = blake3::Hasher::new();
    h.update(b"deos-mail:office:v1");
    h.update(owner.as_bytes());
    h.update(&magic.to_le_bytes());
    let pk = *h.finalize().as_bytes();
    let mut token = [0u8; 32];
    token[..8].copy_from_slice(&magic.to_le_bytes());
    (pk, token)
}

/// The pre-image the single town-wide ferry (postmaster) is addressed over.
fn ferry_keys() -> ([u8; 32], [u8; 32]) {
    let mut h = blake3::Hasher::new();
    h.update(b"deos-mail:ferry:v1");
    let pk = *h.finalize().as_bytes();
    (pk, [0u8; 32])
}

/// The pre-image a letter is addressed over — from + to + the sender's outbox sequence +
/// a collision salt, so successive letters between the same pair get distinct ids.
fn letter_keys(from: CellId, to: CellId, seq: u64, salt: u64) -> ([u8; 32], [u8; 32]) {
    let mut h = blake3::Hasher::new();
    h.update(b"deos-mail:letter:v1");
    h.update(from.as_bytes());
    h.update(to.as_bytes());
    h.update(&seq.to_le_bytes());
    h.update(&salt.to_le_bytes());
    let pk = *h.finalize().as_bytes();
    let mut token = [0u8; 32];
    token[..8].copy_from_slice(&seq.to_le_bytes());
    (pk, token)
}

/// The deterministic id of an address's INBOX cell (whether or not it is installed yet).
pub fn inbox_cell(owner: CellId) -> CellId {
    let (pk, token) = office_keys(owner, MAIL_INBOX_MAGIC);
    CellId::derive_raw(&pk, &token)
}

/// The deterministic id of an address's OUTBOX cell.
pub fn outbox_cell(owner: CellId) -> CellId {
    let (pk, token) = office_keys(owner, MAIL_OUTBOX_MAGIC);
    CellId::derive_raw(&pk, &token)
}

/// The deterministic id of the town-wide FERRY (postmaster / mailman) cell.
pub fn ferry_cell() -> CellId {
    let (pk, token) = ferry_keys();
    CellId::derive_raw(&pk, &token)
}

// ─────────────────────────────────────────────────────────────────────────────
// Errors — human, per the HIG (never "T1 REJECT").
// ─────────────────────────────────────────────────────────────────────────────

/// Why a Letter-Office action was refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MailError {
    /// No letter cell with that id lives on the World.
    UnknownLetter,
    /// The letter is not Outbound — it was already delivered (or is a draft), so there is
    /// nothing for the ferry to move. Nothing committed.
    NotOutbound(LetterStatus),
    /// The letter's routed addresses could not be read back off its heap (a corrupt or
    /// non-letter cell). Nothing committed.
    Unaddressed,
    /// The verified executor rejected the (authorized) turn — the ocap/verification
    /// guarantee firing. Carries the executor's reason.
    Rejected(String),
}

impl std::fmt::Display for MailError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MailError::UnknownLetter => write!(f, "no such letter on the World"),
            MailError::NotOutbound(s) => {
                write!(
                    f,
                    "that letter is {s:?}, not awaiting the ferry — nothing to deliver"
                )
            }
            MailError::Unaddressed => write!(f, "that cell carries no routable letter address"),
            MailError::Rejected(e) => write!(f, "the delivery turn was refused: {e}"),
        }
    }
}
impl std::error::Error for MailError {}

// ─────────────────────────────────────────────────────────────────────────────
// The legible model — what the Mail Room renders (pure, built from the World).
// ─────────────────────────────────────────────────────────────────────────────

/// Where a letter is in its delivery life. `Outbound` sits in the sender's outbox awaiting
/// the ferry; `Delivered` has landed in the recipient's inbox (moved by a receipted turn).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LetterStatus {
    /// Composed but not yet posted (reserved; [`send_letter`] posts as `Outbound` at once).
    Draft,
    /// Posted — sitting in the sender's outbox, awaiting the ferry's round.
    Outbound,
    /// Delivered — moved into the recipient's inbox by a receipted delivery turn.
    Delivered,
}

impl LetterStatus {
    fn from_u64(v: u64) -> LetterStatus {
        match v {
            0 => LetterStatus::Draft,
            2 => LetterStatus::Delivered,
            _ => LetterStatus::Outbound,
        }
    }
    fn as_u64(self) -> u64 {
        match self {
            LetterStatus::Draft => 0,
            LetterStatus::Outbound => 1,
            LetterStatus::Delivered => 2,
        }
    }
    /// A one-word caption for the status chip.
    pub fn label(self) -> &'static str {
        match self {
            LetterStatus::Draft => "draft",
            LetterStatus::Outbound => "outbound",
            LetterStatus::Delivered => "delivered",
        }
    }
}

/// One letter, read off the live World: the cell that IS it, its addresses, its content,
/// and the on-ledger witnesses of its journey. Built purely from the ledger — a letter you
/// can see here is a cell a real turn committed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LetterView {
    /// The letter cell's id (open it in the World Explorer — the letter IS this cell).
    pub cell: CellId,
    /// The full sender address (routed off the letter's heap).
    pub from: CellId,
    /// The full recipient address.
    pub to: CellId,
    /// The subject line (content, from the heap).
    pub subject: String,
    /// The markdown body (content, from the heap).
    pub body: String,
    /// The committed low-8 blake3 digest of the body (the unforgeable content anchor).
    pub digest: u64,
    /// Where the letter is in its journey.
    pub status: LetterStatus,
    /// The World height at which it was posted to the outbox.
    pub sent_at: u64,
    /// The World height at which it was delivered (0 while still Outbound).
    pub delivered_at: u64,
}

impl LetterView {
    /// Does the committed digest still match the body content? (The verify-delivery tooth:
    /// recompute blake3 over the body the heap carries and compare to the slot the turn
    /// committed — the body cannot be altered after delivery without breaking this.)
    pub fn digest_matches(&self) -> bool {
        body_digest_lo(&self.body) == self.digest
    }
}

/// One address's whole correspondence, derived from the live World: the letters in its
/// inbox (delivered TO it), the letters in its outbox (sent FROM it, delivered or still
/// pending), and the office cells' on-ledger tallies.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MailboxView {
    /// The address this mailbox belongs to.
    pub owner: CellId,
    /// The letters delivered to this address, newest first.
    pub inbox: Vec<LetterView>,
    /// The letters this address has sent, newest first (Outbound + Delivered).
    pub outbox: Vec<LetterView>,
    /// The inbox office cell's committed received count (the address's own tally).
    pub received: u64,
    /// The outbox office cell's committed sent count.
    pub sent: u64,
    /// The outbox office cell's committed pending count (still awaiting the ferry).
    pub pending: u64,
}

// ─────────────────────────────────────────────────────────────────────────────
// Reflective reads — the town, off the live ledger (never a cache).
// ─────────────────────────────────────────────────────────────────────────────

/// Is `cell` one of the Letter Office's own cells (a letter / inbox / outbox / ferry)? A
/// surface that wants to hide the mail plumbing from an ordinary cell census can skip these.
pub fn is_mail_cell(world: &World, cell: &CellId) -> bool {
    world
        .ledger()
        .get(cell)
        .map(|c| {
            let kind = unpack_u64(&c.state.fields[SLOT_O_KIND]);
            kind == MAIL_LETTER_MAGIC
                || kind == MAIL_INBOX_MAGIC
                || kind == MAIL_OUTBOX_MAGIC
                || kind == MAIL_FERRY_MAGIC
        })
        .unwrap_or(false)
}

/// Read the letter cell `cell` into a [`LetterView`], or `None` if it is not a letter.
pub fn read_letter(world: &World, cell: CellId) -> Option<LetterView> {
    let c = world.ledger().get(&cell)?;
    if unpack_u64(&c.state.fields[SLOT_L_KIND]) != MAIL_LETTER_MAGIC {
        return None;
    }
    let heap = &c.state.heap_map;
    let body_len = unpack_u64(&c.state.fields[SLOT_L_BODY_LEN]) as usize;
    let subj_len = unpack_u64(&c.state.fields[SLOT_L_SUBJ_LEN]) as usize;
    let from = read_addr(heap, 0)?;
    let to = read_addr(heap, 1)?;
    let body = String::from_utf8_lossy(&read_bytes(heap, COL_BODY, body_len)).into_owned();
    let subject = String::from_utf8_lossy(&read_bytes(heap, COL_SUBJECT, subj_len)).into_owned();
    Some(LetterView {
        cell,
        from,
        to,
        subject,
        body,
        digest: unpack_u64(&c.state.fields[SLOT_L_DIGEST]),
        status: LetterStatus::from_u64(unpack_u64(&c.state.fields[SLOT_L_STATUS])),
        sent_at: unpack_u64(&c.state.fields[SLOT_L_SENT_AT]),
        delivered_at: unpack_u64(&c.state.fields[SLOT_L_DELIVERED_AT]),
    })
}

/// Every letter in the town, newest-sent first — the whole mail-ledger, off the live World.
/// This IS the "Ledger" face: each row is a letter cell a real turn committed.
pub fn town_letters(world: &World) -> Vec<LetterView> {
    let mut letters: Vec<LetterView> = world
        .ledger()
        .iter()
        .filter(|(_, c)| unpack_u64(&c.state.fields[SLOT_L_KIND]) == MAIL_LETTER_MAGIC)
        .filter_map(|(id, _)| read_letter(world, *id))
        .collect();
    // Newest first: by sent height, the cell id as the stable tie-break.
    letters.sort_by(|a, b| {
        b.sent_at
            .cmp(&a.sent_at)
            .then(a.cell.as_bytes().cmp(b.cell.as_bytes()))
    });
    letters
}

/// Read an office cell's slot (0 if the office is not installed).
fn office_slot(world: &World, office: CellId, slot: usize) -> u64 {
    world
        .ledger()
        .get(&office)
        .map(|c| unpack_u64(&c.state.fields[slot]))
        .unwrap_or(0)
}

/// The whole correspondence of `owner`, derived off the live World (never a cache): the
/// inbox (delivered letters addressed to it), the outbox (letters it sent), and the office
/// tallies. An address that never sent or received simply shows an honest empty mailbox.
pub fn mailbox_of(world: &World, owner: CellId) -> MailboxView {
    let all = town_letters(world);
    let inbox: Vec<LetterView> = all
        .iter()
        .filter(|l| l.to == owner && l.status == LetterStatus::Delivered)
        .cloned()
        .collect();
    let outbox: Vec<LetterView> = all.iter().filter(|l| l.from == owner).cloned().collect();
    MailboxView {
        owner,
        inbox,
        outbox,
        received: office_slot(world, inbox_cell(owner), SLOT_O_COUNT),
        sent: office_slot(world, outbox_cell(owner), SLOT_O_COUNT),
        pending: office_slot(world, outbox_cell(owner), SLOT_O_PENDING),
    }
}

/// Every address that has an office in the town (has sent or received at least one letter),
/// most-active first (by the letters it has sent), the id as the stable tie-break. The Mail
/// Room renders these as the correspondent picker.
pub fn correspondents(world: &World) -> Vec<CellId> {
    let mut seen: BTreeMap<CellId, u64> = BTreeMap::new();
    for l in town_letters(world) {
        *seen.entry(l.from).or_default() += 1;
        seen.entry(l.to).or_default();
    }
    let mut v: Vec<(CellId, u64)> = seen.into_iter().collect();
    v.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.as_bytes().cmp(b.0.as_bytes())));
    v.into_iter().map(|(id, _)| id).collect()
}

// ─────────────────────────────────────────────────────────────────────────────
// Installation — the offices + the ferry, on the genesis path (out-of-band, no
// receipt), guarded so a re-open never double-installs.
// ─────────────────────────────────────────────────────────────────────────────

/// Install an office cell (an inbox or outbox) for `owner` if it is not already on the
/// World, carrying its kind marker + owner witness. Returns its id either way. Balance 0
/// so the town leaves the World's Σ-conservation untouched (a seeded 0-balance service
/// cell, like the demo's service anchor).
fn ensure_office_cell(world: &mut World, owner: CellId, ferry: CellId, magic: u64) -> CellId {
    let (pk, token) = office_keys(owner, magic);
    let id = CellId::derive_raw(&pk, &token);
    if !world.ledger().contains(&id) {
        let mut cell = Cell::with_balance(pk, token, 0);
        cell.permissions = open_permissions();
        cell.state.fields[SLOT_O_KIND] = pack_u64(magic);
        cell.state.fields[SLOT_O_OWNER] = pack_u64(id_lo(owner));
        world.genesis_install(cell);
        // AUTHORITY (ocap): acting on a NON-SELF cell needs a held capability —
        // open_permissions on the target is not the authorizing mechanism. Granted
        // exactly once, at creation (before any turn touches the cell, so the
        // durable genesis-mutation guard stays clean): the OWNER drops/drains its
        // own box; the FERRY moves letters through every box on its round.
        world.genesis_grant_cap(&owner, id);
        world.genesis_grant_cap(&ferry, id);
    }
    id
}

/// Ensure `owner` has both office cells (its inbox and its outbox). Returns
/// `(inbox, outbox)`. Idempotent — the guard in [`ensure_office_cell`] makes re-opening a
/// town a no-op.
pub fn ensure_office(world: &mut World, owner: CellId) -> (CellId, CellId) {
    // The ferry must exist first — every office cell grants it a cap at creation
    // so a later delivery round can move letters through the box.
    let ferry = ensure_ferry(world);
    let inbox = ensure_office_cell(world, owner, ferry, MAIL_INBOX_MAGIC);
    let outbox = ensure_office_cell(world, owner, ferry, MAIL_OUTBOX_MAGIC);
    (inbox, outbox)
}

/// Ensure the town-wide ferry (the postmaster / mailman) is installed, and return its id.
/// The ferry agents every delivery turn — Postmark's *Ferry*, the one who runs the round.
pub fn ensure_ferry(world: &mut World) -> CellId {
    let (pk, token) = ferry_keys();
    let id = CellId::derive_raw(&pk, &token);
    if !world.ledger().contains(&id) {
        let mut cell = Cell::with_balance(pk, token, 0);
        cell.permissions = open_permissions();
        cell.state.fields[SLOT_O_KIND] = pack_u64(MAIL_FERRY_MAGIC);
        world.genesis_install(cell);
    }
    id
}

// ─────────────────────────────────────────────────────────────────────────────
// The two motions — SEND (drop in the outbox) and DELIVER (ferry to the inbox).
// ─────────────────────────────────────────────────────────────────────────────

/// The witness a [`send_letter`] / [`deliver_now`] returns — the letter cell that carries
/// it and the receipt hash of the turn that moved it (its line in the unforgeable
/// mail-ledger).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MailReceipt {
    /// The letter cell this motion concerned.
    pub letter: CellId,
    /// The receipt hash of the committed turn (the send-drop, or the ferry delivery).
    pub receipt: [u8; 32],
}

/// **SEND a letter** — compose a new letter cell carrying `body` (markdown) with `subject`
/// from `from` to `to`, and DROP it in `from`'s outbox with a receipted turn. Two motions,
/// in order:
///
///   1. The letter cell is BORN (the genesis path): its markdown body + subject + the
///      routed from/to addresses land in its heap; its from/to/digest/length/`Outbound`
///      status land in its slots; its committed body digest anchors the content.
///   2. A receipted turn agented by the SENDER bumps the sender's OUTBOX office cell —
///      sent += 1, pending += 1, last-peer = `to`, last-digest — the on-ledger record that
///      the letter is now sitting in the outbox awaiting the ferry.
///
/// The letter is content, never a command: the send turn touches only the outbox's tally
/// and the letter's own witnesses; it grants nothing and commands no one (Postmark's rule,
/// and `mailtown`'s proven non-amplification, made mechanical here). Returns the letter
/// cell + the send receipt, or the executor's refusal (nothing committed).
pub fn send_letter(
    world: &mut World,
    from: CellId,
    to: CellId,
    subject: &str,
    body: &str,
) -> Result<MailReceipt, MailError> {
    let (_from_inbox, from_outbox) = ensure_office(world, from);
    ensure_office(world, to);
    ensure_ferry(world);

    let seq = office_slot(world, from_outbox, SLOT_O_COUNT);
    let digest = body_digest_lo(body);
    let sent_at = world.height();

    // 1 ── the letter is born (genesis path; find a free id past any salt collision).
    let mut salt = 0u64;
    let (mut pk, mut token) = letter_keys(from, to, seq, salt);
    let mut letter = CellId::derive_raw(&pk, &token);
    while world.ledger().contains(&letter) {
        salt += 1;
        let keys = letter_keys(from, to, seq, salt);
        pk = keys.0;
        token = keys.1;
        letter = CellId::derive_raw(&pk, &token);
    }
    let mut cell = Cell::with_balance(pk, token, 0);
    cell.permissions = open_permissions();
    cell.state.fields[SLOT_L_KIND] = pack_u64(MAIL_LETTER_MAGIC);
    cell.state.fields[SLOT_L_FROM] = pack_u64(id_lo(from));
    cell.state.fields[SLOT_L_TO] = pack_u64(id_lo(to));
    cell.state.fields[SLOT_L_DIGEST] = pack_u64(digest);
    cell.state.fields[SLOT_L_STATUS] = pack_u64(LetterStatus::Outbound.as_u64());
    cell.state.fields[SLOT_L_BODY_LEN] = pack_u64(body.len() as u64);
    cell.state.fields[SLOT_L_SUBJ_LEN] = pack_u64(subject.len() as u64);
    cell.state.fields[SLOT_L_SENT_AT] = pack_u64(sent_at);
    let mut heap = BTreeMap::new();
    write_bytes(&mut heap, COL_BODY, body.as_bytes());
    write_bytes(&mut heap, COL_SUBJECT, subject.as_bytes());
    heap.insert((COL_ADDR, 0), *from.as_bytes());
    heap.insert((COL_ADDR, 1), *to.as_bytes());
    cell.state.heap_map = heap;
    cell.state.reseal_heap_root();
    world.genesis_install(cell);
    // The ferry flips this letter's status Outbound → Delivered on its round, so it
    // needs a capability to it — granted at birth (before any turn touches it).
    world.genesis_grant_cap(&ferry_cell(), letter);

    // 2 ── drop it in the outbox (a receipted turn agented by the sender; one action on
    // the sender's outbox cell, bumping its sent + pending tallies + the last-peer/digest).
    let pending = office_slot(world, from_outbox, SLOT_O_PENDING) + 1;
    let effects = vec![
        set_slot(from_outbox, SLOT_O_COUNT, seq + 1),
        set_slot(from_outbox, SLOT_O_PENDING, pending),
        set_slot(from_outbox, SLOT_O_LAST_PEER, id_lo(to)),
        set_slot(from_outbox, SLOT_O_LAST_DIGEST, digest),
    ];
    let receipt = commit_forest(world, from, vec![(from_outbox, effects)])?;
    Ok(MailReceipt { letter, receipt })
}

/// **DELIVER a letter NOW** — the ferry's round, fired by hand: MOVE the Outbound letter
/// `letter` from the sender's outbox into the recipient's inbox with ONE receipted turn.
/// The turn, agented by the town's [`ferry_cell`], atomically:
///
///   * flips the LETTER cell's status Outbound → Delivered and stamps its delivered height;
///   * bumps the recipient's INBOX office cell — received += 1, last-sender, last-digest;
///   * drains the sender's OUTBOX office cell — pending -= 1.
///
/// After it commits, the live-World scan ([`mailbox_of`]) places the letter in the
/// recipient's inbox and drops it from the outbox's pending — the letter has *moved*, and
/// the receipt is its unforgeable line in the mail-ledger.
///
/// SEAM (the twice-daily mailman): Postmark's real ferry runs on a cron, twice a day. Here
/// delivery is manual — a `deliver_now` button IS one ferry round. Wiring a scheduler to
/// call this on a cadence (and a git+Postmark federation ferry that writes delivered
/// letters out as markdown files and reads inbound files back in as delivery turns) are the
/// named seams above this on-World mechanic.
pub fn deliver_now(world: &mut World, letter: CellId) -> Result<MailReceipt, MailError> {
    let view = read_letter(world, letter).ok_or(MailError::UnknownLetter)?;
    if view.status != LetterStatus::Outbound {
        return Err(MailError::NotOutbound(view.status));
    }
    let (to_inbox, _to_outbox) = ensure_office(world, view.to);
    let from_outbox = outbox_cell(view.from);
    let ferry = ensure_ferry(world);
    let delivered_at = world.height();
    let pending = office_slot(world, from_outbox, SLOT_O_PENDING).saturating_sub(1);
    let received = office_slot(world, to_inbox, SLOT_O_COUNT) + 1;

    // ONE turn, three cells — the letter moves atomically or not at all (one receipt).
    // A forest of one action PER target cell (the blessed multi-action shape: "several
    // effects, several target cells, one turn, one receipt"), agented by the ferry.
    let actions = vec![
        (
            letter,
            vec![
                set_slot(letter, SLOT_L_STATUS, LetterStatus::Delivered.as_u64()),
                set_slot(letter, SLOT_L_DELIVERED_AT, delivered_at),
            ],
        ),
        (
            to_inbox,
            vec![
                set_slot(to_inbox, SLOT_O_COUNT, received),
                set_slot(to_inbox, SLOT_O_LAST_PEER, id_lo(view.from)),
                set_slot(to_inbox, SLOT_O_LAST_DIGEST, view.digest),
            ],
        ),
        (
            from_outbox,
            vec![set_slot(from_outbox, SLOT_O_PENDING, pending)],
        ),
    ];
    let receipt = commit_forest(world, ferry, actions)?;
    Ok(MailReceipt { letter, receipt })
}

/// A `SetField` effect writing `value` (LE u64) into `slot` of `cell` — the town's one
/// write verb (as in `mailtown`, every state change is a `SetField` on a cell-local slot).
fn set_slot(cell: CellId, slot: usize, value: u64) -> Effect {
    Effect::SetField {
        cell,
        index: slot,
        value: pack_u64(value),
    }
}

/// Commit a receipted FOREST turn agented by `agent` — one action per `(target, effects)`
/// entry (each action acts on its OWN cell, the blessed multi-action shape) — and hand back
/// the receipt hash, or the executor's refusal (nothing committed).
fn commit_forest(
    world: &mut World,
    agent: CellId,
    actions: Vec<(CellId, Vec<Effect>)>,
) -> Result<[u8; 32], MailError> {
    let turn = world.forest_turn(agent, actions);
    match world.commit_turn(turn) {
        crate::world::CommitOutcome::Committed { receipt, .. } => Ok(receipt.receipt_hash()),
        crate::world::CommitOutcome::Rejected { reason, .. } => Err(MailError::Rejected(reason)),
        crate::world::CommitOutcome::Queued { .. } => Err(MailError::Rejected(
            "the World is suspended — the turn was staged".into(),
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::World;

    /// Two residents; a letter posted, then delivered by the ferry — the whole round trip.
    /// The letter is a real cell; the inbox/outbox tallies + statuses tell its journey; the
    /// committed digest still anchors the content.
    #[test]
    fn a_letter_posts_to_the_outbox_then_the_ferry_moves_it_to_the_inbox() {
        let mut w = World::new();
        let ada = w.genesis_cell(0x21, 5_000);
        let boris = w.genesis_cell(0x22, 5_000);

        // POST — the letter is born Outbound, sitting in Ada's outbox; Boris's inbox empty.
        let sent = send_letter(
            &mut w,
            ada,
            boris,
            "hello",
            "# hi boris\n\na letter, in markdown.",
        )
        .expect("the send commits");
        let letter = read_letter(&w, sent.letter).expect("the letter is a real cell");
        assert_eq!(letter.from, ada);
        assert_eq!(letter.to, boris);
        assert_eq!(letter.status, LetterStatus::Outbound);
        assert_eq!(letter.subject, "hello");
        assert_eq!(letter.body, "# hi boris\n\na letter, in markdown.");
        assert!(
            letter.digest_matches(),
            "the committed digest anchors the body"
        );

        let ada_box = mailbox_of(&w, ada);
        assert_eq!(ada_box.sent, 1);
        assert_eq!(ada_box.pending, 1, "one letter awaits the ferry");
        assert_eq!(ada_box.outbox.len(), 1);
        let boris_box = mailbox_of(&w, boris);
        assert!(
            boris_box.inbox.is_empty(),
            "not delivered yet — inbox is empty"
        );
        assert_eq!(boris_box.received, 0);

        // DELIVER — the ferry moves it; now it is in Boris's inbox, out of Ada's pending.
        let del = deliver_now(&mut w, sent.letter).expect("the delivery commits");
        assert_ne!(del.receipt, [0u8; 32], "a real receipt hash");
        assert_ne!(
            del.receipt, sent.receipt,
            "the send + delivery are distinct turns"
        );

        let letter = read_letter(&w, sent.letter).unwrap();
        assert_eq!(letter.status, LetterStatus::Delivered);
        assert!(letter.delivered_at >= letter.sent_at);

        let ada_box = mailbox_of(&w, ada);
        assert_eq!(ada_box.pending, 0, "the outbox drained on delivery");
        assert_eq!(ada_box.sent, 1, "but the sent tally stands");
        let boris_box = mailbox_of(&w, boris);
        assert_eq!(boris_box.received, 1);
        assert_eq!(boris_box.inbox.len(), 1);
        assert_eq!(boris_box.inbox[0].cell, sent.letter);
    }

    /// Delivering a letter twice is refused the second time — it is no longer Outbound, so
    /// the ferry has nothing to move (idempotent, nothing committed).
    #[test]
    fn the_ferry_refuses_to_deliver_an_already_delivered_letter() {
        let mut w = World::new();
        let a = w.genesis_cell(0x31, 5_000);
        let b = w.genesis_cell(0x32, 5_000);
        let sent = send_letter(&mut w, a, b, "s", "body").unwrap();
        deliver_now(&mut w, sent.letter).expect("first delivery commits");
        let again = deliver_now(&mut w, sent.letter);
        assert_eq!(again, Err(MailError::NotOutbound(LetterStatus::Delivered)));
    }

    /// The office / letter ids are deterministic and distinct, and the town-ledger scan
    /// returns every letter newest-first regardless of sender.
    #[test]
    fn addressing_is_deterministic_and_the_town_ledger_scans_every_letter() {
        let mut w = World::new();
        let a = w.genesis_cell(0x41, 5_000);
        let b = w.genesis_cell(0x42, 5_000);

        // Distinct offices per address + role; stable across calls.
        assert_ne!(inbox_cell(a), outbox_cell(a));
        assert_ne!(inbox_cell(a), inbox_cell(b));
        assert_eq!(inbox_cell(a), inbox_cell(a));

        send_letter(&mut w, a, b, "one", "first").unwrap();
        send_letter(&mut w, b, a, "two", "second").unwrap();
        send_letter(&mut w, a, b, "three", "third").unwrap();

        let all = town_letters(&w);
        assert_eq!(all.len(), 3, "every letter is a cell the scan finds");
        // Newest-sent first (heights are monotonic across the three commits).
        assert!(all[0].sent_at >= all[1].sent_at && all[1].sent_at >= all[2].sent_at);

        // Two distinct correspondents, both with offices.
        let who = correspondents(&w);
        assert!(who.contains(&a) && who.contains(&b));

        // Ada's outbox holds both her letters; her inbox is empty until Boris's is ferried.
        let ada_box = mailbox_of(&w, a);
        assert_eq!(ada_box.outbox.len(), 2);
        assert!(ada_box.inbox.is_empty());
    }

    /// A body spanning several 32-byte heap chunks round-trips byte-for-byte (the chunked
    /// heap codec is exact, trailing padding trimmed to the committed length).
    #[test]
    fn a_multi_chunk_markdown_body_round_trips_through_the_heap() {
        let mut w = World::new();
        let a = w.genesis_cell(0x51, 5_000);
        let b = w.genesis_cell(0x52, 5_000);
        let body = format!(
            "# A longer letter\n\n{}",
            "dregg is a verified substrate; a letter is a cell. ".repeat(8)
        );
        let sent = send_letter(
            &mut w,
            a,
            b,
            "a subject that also spans past thirty-two bytes",
            &body,
        )
        .unwrap();
        let got = read_letter(&w, sent.letter).unwrap();
        assert_eq!(got.body, body);
        assert_eq!(
            got.subject,
            "a subject that also spans past thirty-two bytes"
        );
        assert!(got.digest_matches());
    }
}
