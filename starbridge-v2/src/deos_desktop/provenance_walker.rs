//! **THE PROVENANCE WALKER** — walk the World's receipt chain hash-by-hash,
//! every link RECOMPUTED as you walk (never trusted).
//!
//! The desktop already *shows* receipts (the Transcript, the World Explorer's
//! Chronicle) — four hex bytes in a scrolling log, taken on faith. This surface
//! makes the chain itself the object: one row per committed receipt, and for
//! each row the walker RE-DERIVES the two links that make the log a chain
//! instead of a list:
//!
//!   * **the state chain** — this receipt's `pre_state_hash` must equal its
//!     predecessor's `post_state_hash`. Both are full-ledger roots the executor
//!     pinned at commit time (`ledger.root()` before and after the turn), so
//!     consecutive receipts of one World MUST hand the root off gaplessly. (A
//!     genesis install between two commits — a hire's mid-session seed — is a
//!     lawful out-of-band root move; the walk names it
//!     [`LinkVerdict::Reseeded`] off the recorded History instead of crying
//!     broken.)
//!   * **the blocklace back-edge** — this receipt's `previous_receipt_hash`
//!     must equal the blake3 [`TurnReceipt::receipt_hash`] of the SAME AGENT's
//!     previous receipt, recomputed here from the receipt's own fields (the
//!     same per-agent threading `World::commit_turn` performs at commit; the
//!     hash is never read from anywhere — it is re-derived on every walk).
//!
//! A verdict is painted per link ([`LinkVerdict`]): a broken link is loud
//! amber, an origin (nothing before it to chain from) is dim, a verified link
//! is the console's green tick. "The substrate cannot lie" stops being a
//! sentence and becomes a column you can read.
//!
//! ## The clobber-safe split
//!
//! Like [`super::world_explorer`] / [`super::agent_room`], this module is pure
//! presentation plus a small gpui-free model: the walk rows ([`walk_rows`] —
//! the chain-verify core, unit-tested headlessly below), the per-window view
//! state ([`WalkerState`]), and inert element renderers (the header, the rows,
//! the selected receipt's detail face). The desktop View owns the window
//! dispatch and wraps each row in its own `cx.listener` (selection, the
//! walk-back button, the inspector click-through, go-to-that-point) — it holds
//! the `Context` the listeners need; nothing here does. The scroll handles are
//! plain values threaded from the View's [`super::face_scroll`] registry, so
//! each face keeps its place behind a real NT scrollbar.
//!
//! Chrome: the dark console look the Transcript and the Chronicle wear —
//! deep-slate ground, phosphor-green text, cyan rule lines.

use gpui::{div, px, AnyElement, FontWeight, IntoElement, ParentElement, Styled};

use dregg_turn::turn::TurnReceipt;
use dregg_types::CellId;

use crate::deos_desktop::chrome::id_short;
use crate::provenance_navigator::TurnDetail;
use crate::replay::{History, RecordedStep};

// ── The dark console palette (the Transcript/Chronicle dress, named) ──────────────
// The NT accent constants (`chrome::NT_OK` = 0x0a7a2a …) are inked for the light
// button-face panels; on the console's deep-slate ground they'd read as mud. These
// are the SAME hues the Transcript already paints, plus bright verdict accents
// legible on dark.

/// The console ground — the Transcript's deep slate.
pub const CONSOLE_BG: u32 = 0x101820;
/// The console body text — the Transcript's phosphor green.
pub const CONSOLE_TEXT: u32 = 0x9fe0a0;
/// The console rule/heading — the Transcript's cyan.
pub const CONSOLE_HEAD: u32 = 0x6fc0ff;
/// A verified link's tick — bright green, legible on the dark ground.
pub const CONSOLE_OK: u32 = 0x50e070;
/// A broken/deferred link — bright amber (the loud verdict).
pub const CONSOLE_WARN: u32 = 0xffb84d;
/// A dim annotation (origins, effect summaries, computrons).
pub const CONSOLE_DIM: u32 = 0x5f7f6f;
/// The selected row's fill — a navy console highlight.
pub const CONSOLE_SEL: u32 = 0x1e3a5f;

/// The deterministic anchor cell the desktop hosts the Provenance Walker window
/// under — a distinct non-ledger sentinel (the [`super::agent_room`] idiom) so
/// the walker opens as its OWN window keyed apart from any inspectable cell.
pub fn walker_window_cell() -> CellId {
    CellId::from_bytes([0x9Bu8; 32]) // '9B' — the chain-walk sentinel
}

/// Whether `cell` keys the Provenance Walker window (drives the pane title).
pub fn is_walker(cell: &CellId) -> bool {
    cell == &walker_window_cell()
}

// ===========================================================================
// The chain-verify core — pure, gpui-free, unit-tested below.
// ===========================================================================

/// The verdict on ONE recomputed link of the chain. Verification means
/// RE-DERIVED AND MATCHED — a link we could not check is named as such, never
/// silently passed off as green.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LinkVerdict {
    /// Nothing before this link to chain from — the log's first receipt (state
    /// chain) or the agent's first turn with an honest `None` back-edge
    /// (blocklace). Trivially sound; drawn dim, not green.
    Origin,
    /// Recomputed and MATCHED — blake3 re-derived from the predecessor's own
    /// fields (or the roots compared), then found equal. The green tick.
    Verified,
    /// Recomputed and MISMATCHED — a broken chain. The loud amber verdict.
    Broken,
    /// One side is the symbolic-mode DEFERRED sentinel
    /// ([`dregg_turn::collapse::DEFERRED_STATE_HASH`]) — there is no real
    /// witness to compare until `World::collapse` materializes it. NOT
    /// verified (and [`chain_verifies_to_depth`] refuses it).
    Deferred,
    /// The back-edge points BEFORE this log's first receipt (a truncated log):
    /// the predecessor is not in hand, so the link is walkable only with the
    /// full chain. NOT verified.
    Unanchored,
    /// A GENESIS INSTALL landed between this receipt and its predecessor
    /// (`World::genesis_cell` — the executor-bypassing seed path the hireling's
    /// hire uses mid-session). The ledger root legitimately moved out-of-band,
    /// so the state handoff is NOT comparable here — named honestly instead of
    /// crying BROKEN on a lawful world. Counts as sound (like an origin,
    /// there is nothing to compare); the recorded History still root-verifies
    /// the install itself on replay.
    Reseeded,
}

impl LinkVerdict {
    /// Whether this link counts as VERIFIED (recomputed + matched, or a link
    /// with genuinely nothing to compare — an origin / a reseed boundary).
    /// `Deferred`/`Unanchored`/`Broken` all fail — verification means
    /// verified, not "not known broken".
    pub fn is_sound(self) -> bool {
        matches!(
            self,
            LinkVerdict::Origin | LinkVerdict::Verified | LinkVerdict::Reseeded
        )
    }

    /// The one-glyph console tick for this verdict (font-safe: the desktop
    /// already paints ✓/✗ in the rewind rail + workflow verdicts).
    pub fn tick(self) -> &'static str {
        match self {
            LinkVerdict::Origin => "·",
            LinkVerdict::Verified => "✓",
            LinkVerdict::Broken => "✗",
            LinkVerdict::Deferred => "?",
            LinkVerdict::Unanchored => "…",
            LinkVerdict::Reseeded => "+",
        }
    }

    /// The console color this verdict paints in.
    pub fn color(self) -> u32 {
        match self {
            LinkVerdict::Origin | LinkVerdict::Reseeded => CONSOLE_DIM,
            LinkVerdict::Verified => CONSOLE_OK,
            _ => CONSOLE_WARN,
        }
    }
}

/// One row of the walk — a committed receipt with BOTH its links re-derived.
/// Built by [`walk_rows`]; the View paints one clickable row per entry and the
/// detail face for the selected one.
#[derive(Clone, Debug)]
pub struct WalkRow {
    /// The receipt's position in the World's receipt log (0-based).
    pub index: usize,
    /// The authoring agent (the receipt's `agent` — whose chain this rode).
    pub agent: CellId,
    /// The turn hash the receipt attests (shown as the row's left hash).
    pub turn_hash: [u8; 32],
    /// The post-state ledger root the executor pinned after this turn.
    pub post_state_hash: [u8; 32],
    /// The receipt hash — RECOMPUTED here (blake3 over the receipt's fields),
    /// never read from a cache. This is the hash the successor's back-edge
    /// must name.
    pub receipt_hash: [u8; 32],
    /// The recorded back-edge to the same agent's previous receipt, verbatim.
    pub previous_receipt: Option<[u8; 32]>,
    /// The metered cost the executor charged.
    pub computrons: u64,
    /// The human effects summary (the recorded turn's effect kinds, or an
    /// action-count fallback when no recorded turn is in hand).
    pub effects: String,
    /// The STATE-CHAIN verdict: `pre_state_hash == predecessor.post_state_hash`.
    pub state_link: LinkVerdict,
    /// The BLOCKLACE verdict: `previous_receipt_hash == recomputed hash of the
    /// same agent's previous receipt`.
    pub agent_link: LinkVerdict,
}

/// Hex of the first 4 bytes of a hash — the console's dense hash chip (the
/// Transcript's own format).
pub fn hash4(h: &[u8; 32]) -> String {
    h[..4].iter().map(|b| format!("{b:02x}")).collect()
}

/// Which receipts follow an out-of-band GENESIS install — `out[i]` is true iff
/// at least one [`RecordedStep::Genesis`] landed between receipt `i-1`'s commit
/// and receipt `i`'s (installs before the FIRST commit shape row 0, which is an
/// origin anyway). Built from the SAME recorded [`History`] the rewind rail
/// replays; the state handoff across such a boundary legitimately moved
/// without a turn, so [`walk_rows`] names it [`LinkVerdict::Reseeded`] instead
/// of crying BROKEN on a lawful world. PURE.
pub fn reseeded_flags(history: &History) -> Vec<bool> {
    let mut out = Vec::new();
    let mut pending = false;
    for step in history.steps() {
        match step {
            RecordedStep::Genesis { .. } => pending = true,
            RecordedStep::Committed { .. } => {
                // Installs before the FIRST commit are world setup shaping row 0
                // (an origin anyway), not a mid-session reseed boundary.
                out.push(pending && !out.is_empty());
                pending = false;
            }
        }
    }
    out
}

/// **Build the walk** — one [`WalkRow`] per receipt, both links RE-DERIVED.
///
/// `effects` carries one summary line per receipt in log order (the caller
/// builds it from the recorded turns' effect kinds — see
/// [`crate::provenance_navigator::effect_kinds`]); a receipt past the slice's
/// end (e.g. a symbolic-mode commit the replay tape skipped) falls back to its
/// own `action_count`. `reseeded` marks the receipts that follow an
/// out-of-band genesis install ([`reseeded_flags`]); past-the-end reads as
/// false. PURE — never mutates, never trusts.
pub fn walk_rows(receipts: &[TurnReceipt], effects: &[String], reseeded: &[bool]) -> Vec<WalkRow> {
    // Recompute EVERY receipt hash once (blake3 over each receipt's own
    // fields) — the single source every back-edge check below compares against.
    let recomputed: Vec<[u8; 32]> = receipts.iter().map(|r| r.receipt_hash()).collect();

    // The most recent receipt index per agent, threaded forward — the same
    // walk `World::commit_turn` does through `get_last_receipt_hash`.
    let mut last_of_agent: std::collections::HashMap<CellId, usize> =
        std::collections::HashMap::new();

    let deferred = dregg_turn::collapse::DEFERRED_STATE_HASH;
    let mut out = Vec::with_capacity(receipts.len());
    for (i, r) in receipts.iter().enumerate() {
        // ── the state chain: post[i-1] must hand pre[i] the root, gaplessly —
        //    except across a genesis-install boundary, where the root lawfully
        //    moved without a turn (named, never compared into a false BROKEN).
        let state_link = if i == 0 {
            LinkVerdict::Origin
        } else if r.pre_state_hash == deferred || receipts[i - 1].post_state_hash == deferred {
            LinkVerdict::Deferred
        } else if reseeded.get(i).copied().unwrap_or(false) {
            LinkVerdict::Reseeded
        } else if r.pre_state_hash == receipts[i - 1].post_state_hash {
            LinkVerdict::Verified
        } else {
            LinkVerdict::Broken
        };

        // ── the blocklace back-edge: the agent's OWN previous receipt,
        //    recomputed, must be what this receipt names.
        let agent_link = match (last_of_agent.get(&r.agent), r.previous_receipt_hash) {
            // First turn of this agent in the log, honest None back-edge.
            (None, None) => LinkVerdict::Origin,
            // A back-edge into history this log does not hold (truncated log).
            (None, Some(_)) => LinkVerdict::Unanchored,
            // The agent has a prior receipt here but this one disowns it.
            (Some(_), None) => LinkVerdict::Broken,
            (Some(&j), Some(prev)) => {
                if prev == recomputed[j] {
                    LinkVerdict::Verified
                } else {
                    LinkVerdict::Broken
                }
            }
        };
        last_of_agent.insert(r.agent, i);

        let effects_line = effects.get(i).cloned().unwrap_or_else(|| {
            format!(
                "{} action{}",
                r.action_count,
                if r.action_count == 1 { "" } else { "s" }
            )
        });

        out.push(WalkRow {
            index: i,
            agent: r.agent,
            turn_hash: r.turn_hash,
            post_state_hash: r.post_state_hash,
            receipt_hash: recomputed[i],
            previous_receipt: r.previous_receipt_hash,
            computrons: r.computrons_used,
            effects: effects_line,
            state_link,
            agent_link,
        });
    }
    out
}

/// **The bake's tooth** — does the chain VERIFY to depth `n`? Re-derives every
/// link ([`walk_rows`]) and demands the NEWEST `n` receipts' links all be sound
/// ([`LinkVerdict::is_sound`]: recomputed-and-matched, or a link with truly
/// nothing to compare — an origin / a named reseed boundary). A deferred
/// witness, an unanchored back-edge, or any mismatch fails — the assertion is
/// "verified", never "not known broken". `n` larger than the log checks the
/// whole log; an empty log verifies vacuously (nothing to break). `reseeded`
/// is [`reseeded_flags`]' output (empty when no history is in hand — strictest).
pub fn chain_verifies_to_depth(receipts: &[TurnReceipt], reseeded: &[bool], n: usize) -> bool {
    let rows = walk_rows(receipts, &[], reseeded);
    let start = rows.len().saturating_sub(n);
    rows[start..]
        .iter()
        .all(|r| r.state_link.is_sound() && r.agent_link.is_sound())
}

/// `(sound, total)` link counts across the walk — the header's at-a-glance
/// verdict (each row carries two links; both must be sound to count clean).
pub fn link_counts(rows: &[WalkRow]) -> (usize, usize) {
    let sound = rows
        .iter()
        .filter(|r| r.state_link.is_sound() && r.agent_link.is_sound())
        .count();
    (sound, rows.len())
}

// ===========================================================================
// The per-window view state.
// ===========================================================================

/// The per-window view state of a Provenance Walker — the walk cursor (which
/// receipt is selected, keyed by RECOMPUTED hash so the cursor survives new
/// commits appending below it) and the last go-to-that-point landing. The
/// desktop holds this keyed by the walker's sentinel cell. A pure view concern.
#[derive(Clone, Default)]
pub struct WalkerState {
    /// The selected receipt (the walk cursor) — `None` follows the head.
    pub selected: Option<[u8; 32]>,
    /// The last "go to that point" landing over the selected receipt, if any.
    pub landed: Option<GotoNote>,
}

/// The view-side note of a root-verified replay landing (built by the View
/// from [`crate::provenance_navigator::goto`]'s `GotoCursor` — the fields the
/// detail face paints, gpui-free and cheap to clone).
#[derive(Clone, Debug)]
pub struct GotoNote {
    /// The `History` step the landing sits at.
    pub step: usize,
    /// The canonical ledger root recorded at the landing (the verified tooth).
    pub root: [u8; 32],
    /// Whether the reconstruction root-VERIFIED against the recorded tooth.
    pub verified: bool,
    /// Whether the landing IS the live head (else a re-derived past).
    pub live: bool,
    /// The authoring agent's reconstructed balance at the landing, if it
    /// existed then — the then-vs-now teeth.
    pub balance_then: Option<i64>,
}

// ===========================================================================
// The pure renderers — inert element trees; the View adds the listeners.
// ===========================================================================

/// The console heading over the walk: receipt count, links-verified tally
/// (green when every link re-derived clean, amber otherwise), world height.
pub fn render_walker_header(rows: &[WalkRow], height: u64) -> AnyElement {
    let (sound, total) = link_counts(rows);
    let all_clean = sound == total;
    let verdict_color = if all_clean { CONSOLE_OK } else { CONSOLE_WARN };
    div()
        .flex()
        .flex_col()
        .child(div().text_color(gpui::rgb(CONSOLE_HEAD)).child(format!(
            "── receipt chain · {total} receipts · height {height} "
        )))
        .child(
            div()
                .text_size(px(10.0))
                .text_color(gpui::rgb(verdict_color))
                .child(if total == 0 {
                    "no receipts yet — actuate a cell, then walk its chain".to_string()
                } else {
                    format!(
                        "{} — {sound}/{total} rows re-derived clean (state root handoff ✓ · blocklace back-edge ✓)",
                        if all_clean { "chain VERIFIED" } else { "chain BROKEN" },
                    )
                }),
        )
        .into_any_element()
}

/// One INERT walk row — the dense console line: index, both link ticks, the
/// `turn → post` hash pair, the recomputed receipt hash, the agent, effects,
/// computrons. No click wiring: the View wraps this in its own listener div
/// (the [`super::spotter::render_spotter_rows`] discipline) and paints the
/// selection fill on the wrapper.
pub fn render_walk_row(row: &WalkRow, selected: bool) -> AnyElement {
    let text = if selected { 0xffffff } else { CONSOLE_TEXT };
    div()
        .flex()
        .flex_row()
        .gap_1()
        .text_size(px(11.0))
        .text_color(gpui::rgb(text))
        .child(
            div()
                .w(px(34.0))
                .flex_none()
                .text_color(gpui::rgb(CONSOLE_DIM))
                .child(format!("#{}", row.index)),
        )
        // The two recomputed-link ticks — state-chain first, back-edge second.
        .child(
            div()
                .w(px(16.0))
                .flex_none()
                .text_color(gpui::rgb(row.state_link.color()))
                .child(row.state_link.tick()),
        )
        .child(
            div()
                .w(px(16.0))
                .flex_none()
                .text_color(gpui::rgb(row.agent_link.color()))
                .child(row.agent_link.tick()),
        )
        .child(div().flex_none().child(format!(
            "turn {} → post {}",
            hash4(&row.turn_hash),
            hash4(&row.post_state_hash)
        )))
        .child(
            div()
                .flex_none()
                .text_color(gpui::rgb(CONSOLE_HEAD))
                .child(format!("rcpt {}", hash4(&row.receipt_hash))),
        )
        .child(
            div()
                .flex_none()
                .font_weight(FontWeight::BOLD)
                .child(id_short(&row.agent)),
        )
        .child(
            div()
                .flex_1()
                .text_color(gpui::rgb(CONSOLE_DIM))
                .child(format!("{} · {}cu", row.effects, row.computrons)),
        )
        .into_any_element()
}

/// The selected receipt's DETAIL face — the full attestation surface off the
/// real [`TurnDetail`] (author, height/step, timestamp, cost, every effect)
/// plus the recomputed-link verdicts and, when the View has landed a
/// go-to-that-point, the root-verified landing note. Inert; the View mounts
/// its walk-back / inspect / goto buttons beside this.
pub fn render_detail_face(
    detail: &TurnDetail,
    row: &WalkRow,
    landed: Option<&GotoNote>,
) -> AnyElement {
    let mut col = div()
        .flex()
        .flex_col()
        .gap_1()
        .text_size(px(11.0))
        .text_color(gpui::rgb(CONSOLE_TEXT))
        .child(
            div()
                .text_color(gpui::rgb(CONSOLE_HEAD))
                .child(format!("── receipt {} · detail ", hash4(&row.receipt_hash))),
        )
        .child(detail_row(
            "author",
            &format!("{} (agent cell)", id_short(&detail.author)),
            CONSOLE_TEXT,
        ))
        .child(detail_row(
            "height",
            &format!("{} (history step {})", detail.height, detail.step),
            CONSOLE_TEXT,
        ))
        .child(detail_row(
            "timestamp",
            &detail.timestamp.to_string(),
            CONSOLE_TEXT,
        ))
        .child(detail_row(
            "cost",
            &format!(
                "{}cu · {} effect(s)",
                detail.computrons_used, detail.effect_count
            ),
            CONSOLE_TEXT,
        ))
        .child(detail_row(
            "state chain",
            &format!(
                "{} pre ← post handoff {}",
                row.state_link.tick(),
                verdict_word(row.state_link)
            ),
            row.state_link.color(),
        ))
        .child(detail_row(
            "back-edge",
            &match row.previous_receipt {
                Some(p) => format!(
                    "{} ← previous receipt {} {}",
                    row.agent_link.tick(),
                    hash4(&p),
                    verdict_word(row.agent_link)
                ),
                None => format!(
                    "{} chain head — no previous receipt ({})",
                    row.agent_link.tick(),
                    verdict_word(row.agent_link)
                ),
            },
            row.agent_link.color(),
        ));

    for e in &detail.effects {
        let cells: Vec<String> = e.cells.iter().map(id_short).collect();
        let mut line = format!("  {} {}", e.kind, cells.join(" → "));
        if !e.summary.is_empty() {
            line.push_str(&format!(" · {}", e.summary));
        }
        col = col.child(
            div()
                .text_color(gpui::rgb(CONSOLE_DIM))
                .text_size(px(10.0))
                .child(line),
        );
    }

    if let Some(g) = landed {
        let color = if g.verified { CONSOLE_OK } else { CONSOLE_WARN };
        col = col
            .child(
                div()
                    .text_color(gpui::rgb(CONSOLE_HEAD))
                    .child("── go to that point · root-verified replay "),
            )
            .child(detail_row(
                "landing",
                &format!(
                    "step {} · root {} · {} · {}",
                    g.step,
                    hash4(&g.root),
                    if g.verified {
                        "✓ VERIFIED against the recorded tooth"
                    } else {
                        "✗ FAILED to verify"
                    },
                    if g.live { "LIVE head" } else { "replayed past" },
                ),
                color,
            ));
        if let Some(bal) = g.balance_then {
            col = col.child(detail_row(
                "author then",
                &format!("balance {bal} at that point"),
                CONSOLE_TEXT,
            ));
        }
    }
    col.into_any_element()
}

/// A `key · value` console detail row (the dark-ground sibling of
/// `chrome::face_row_color`).
fn detail_row(key: &str, value: &str, color: u32) -> AnyElement {
    div()
        .flex()
        .flex_row()
        .gap_1()
        .text_size(px(11.0))
        .child(
            div()
                .w(px(84.0))
                .flex_none()
                .text_color(gpui::rgb(CONSOLE_DIM))
                .child(key.to_string()),
        )
        .child(
            div()
                .flex_1()
                .text_color(gpui::rgb(color))
                .child(value.to_string()),
        )
        .into_any_element()
}

/// The verdict, worded for a detail row.
fn verdict_word(v: LinkVerdict) -> &'static str {
    match v {
        LinkVerdict::Origin => "(origin — nothing before it)",
        LinkVerdict::Verified => "RECOMPUTED · MATCHED",
        LinkVerdict::Broken => "RECOMPUTED · MISMATCH — BROKEN",
        LinkVerdict::Deferred => "(deferred witness — unverifiable here)",
        LinkVerdict::Unanchored => "(back-edge precedes this log)",
        LinkVerdict::Reseeded => "(genesis install landed between — root moved without a turn)",
    }
}

// ===========================================================================
// TESTS — gpui-free over the chain-verify core, exactly as
// provenance_navigator.rs / rewind.rs test theirs. The Worlds are real; the
// tampering is ours.
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::{transfer, World};

    /// A world with TWO agents interleaved: treasury acts, user acts, treasury
    /// acts again — so the per-agent back-edge threading crosses the global
    /// log order (the blocklace, not a single chain).
    fn two_agent_world() -> (World, CellId, CellId) {
        let mut w = World::new();
        let treasury = w.genesis_cell(0x11, 1_000);
        let user = w.genesis_cell(0x22, 0);
        let t1 = w.turn(treasury, vec![transfer(treasury, user, 100)]);
        assert!(w.commit_turn(t1).is_committed());
        let t2 = w.turn(user, vec![transfer(user, treasury, 30)]);
        assert!(w.commit_turn(t2).is_committed());
        let t3 = w.turn(treasury, vec![transfer(treasury, user, 50)]);
        assert!(w.commit_turn(t3).is_committed());
        (w, treasury, user)
    }

    #[test]
    fn walk_rows_verifies_a_real_chain_end_to_end() {
        let (w, treasury, user) = two_agent_world();
        let rows = walk_rows(w.receipts(), &[], &[]);
        assert_eq!(rows.len(), 3);

        // Row 0: the log's first receipt — state origin, agent origin.
        assert_eq!(rows[0].state_link, LinkVerdict::Origin);
        assert_eq!(rows[0].agent_link, LinkVerdict::Origin);
        assert_eq!(rows[0].agent, treasury);

        // Row 1: the USER's first turn — state chain verified against row 0's
        // post root; back-edge is the user's own origin (None), NOT row 0's.
        assert_eq!(rows[1].state_link, LinkVerdict::Verified);
        assert_eq!(rows[1].agent_link, LinkVerdict::Origin);
        assert_eq!(rows[1].agent, user);

        // Row 2: treasury's SECOND turn — both links recompute and match:
        // pre(2) == post(1), and the back-edge names row 0's RECOMPUTED hash.
        assert_eq!(rows[2].state_link, LinkVerdict::Verified);
        assert_eq!(rows[2].agent_link, LinkVerdict::Verified);
        assert_eq!(rows[2].previous_receipt, Some(rows[0].receipt_hash));

        let (sound, total) = link_counts(&rows);
        assert_eq!((sound, total), (3, 3), "every row re-derives clean");
    }

    #[test]
    fn chain_verifies_to_depth_walks_from_the_head() {
        let (w, ..) = two_agent_world();
        // Every depth verifies on an untampered log — including depths past
        // the log's start (they clamp to the whole log) and 0 (vacuous).
        for n in [0usize, 1, 2, 3, 64] {
            assert!(
                chain_verifies_to_depth(w.receipts(), &[], n),
                "depth {n} must verify on the real chain"
            );
        }
        // The empty log verifies vacuously.
        assert!(chain_verifies_to_depth(&[], &[], 8));
    }

    #[test]
    fn a_tampered_post_root_breaks_the_walk_where_it_lies() {
        let (w, ..) = two_agent_world();
        let mut receipts = w.receipts().to_vec();
        // Tamper the MIDDLE receipt's post-state root (the substituted-state
        // attack the chain exists to catch).
        receipts[1].post_state_hash[0] ^= 0xFF;

        let rows = walk_rows(&receipts, &[], &[]);
        // The successor's state handoff no longer matches the tampered root.
        assert_eq!(rows[2].state_link, LinkVerdict::Broken);
        // AND the tampered receipt's recomputed hash changed, so the head's
        // back-edge... names row 0 (same agent), which is untampered — the
        // state chain alone catches this one.
        assert!(
            !chain_verifies_to_depth(&receipts, &[], 2),
            "the head's window sees the break"
        );
        // A depth-1 walk stops before the broken link (row 2's own links are
        // what depth 1 checks — its state link IS the broken one).
        assert!(!chain_verifies_to_depth(&receipts, &[], 1));
    }

    #[test]
    fn a_tampered_receipt_field_breaks_the_back_edge() {
        let (w, ..) = two_agent_world();
        let mut receipts = w.receipts().to_vec();
        // Tamper a HASHED field of the treasury's FIRST receipt (the metered
        // cost — bound into receipt_hash v3). Its recomputed hash shifts, so
        // the treasury's SECOND receipt's back-edge no longer matches: the
        // forgery is caught by RECOMPUTING, exactly the never-trust discipline.
        receipts[0].computrons_used += 1;

        let rows = walk_rows(&receipts, &[], &[]);
        assert_eq!(rows[2].agent_link, LinkVerdict::Broken);
        assert!(!chain_verifies_to_depth(&receipts, &[], 1));
        assert!(!chain_verifies_to_depth(&receipts, &[], 3));
        // The untampered suffix of ANOTHER agent still verifies at depth 2:
        // rows 1 and 2 — no: row 2's back-edge is broken, so only depth 0 is
        // clean. Depth 0 (vacuous) passes; anything touching row 2 fails.
        assert!(chain_verifies_to_depth(&receipts, &[], 0));
    }

    #[test]
    fn a_disowned_back_edge_is_broken_and_a_deferred_witness_refuses() {
        let (w, ..) = two_agent_world();

        // Disown: the treasury's second receipt claims NO predecessor while
        // its agent demonstrably has one in the log.
        let mut disowned = w.receipts().to_vec();
        disowned[2].previous_receipt_hash = None;
        let rows = walk_rows(&disowned, &[], &[]);
        assert_eq!(rows[2].agent_link, LinkVerdict::Broken);

        // Deferred: a symbolic-mode sentinel witness is UNVERIFIABLE, and the
        // depth assertion refuses it (verification means verified).
        let mut deferred = w.receipts().to_vec();
        deferred[1].post_state_hash = dregg_turn::collapse::DEFERRED_STATE_HASH;
        deferred[1].pre_state_hash = dregg_turn::collapse::DEFERRED_STATE_HASH;
        let rows = walk_rows(&deferred, &[], &[]);
        assert_eq!(rows[1].state_link, LinkVerdict::Deferred);
        assert_eq!(rows[2].state_link, LinkVerdict::Deferred);
        assert!(!chain_verifies_to_depth(&deferred, &[], 3));
    }

    #[test]
    fn a_truncated_log_reads_unanchored_not_broken() {
        let (w, ..) = two_agent_world();
        // Drop the log's head — the treasury's second receipt now back-edges
        // into history we do not hold. Honest verdict: Unanchored (walkable
        // only with the full chain), which still FAILS strict verification.
        let truncated = &w.receipts()[1..];
        let rows = walk_rows(truncated, &[], &[]);
        assert_eq!(rows[1].agent_link, LinkVerdict::Unanchored);
        assert!(!chain_verifies_to_depth(truncated, &[], 2));
        // The user's row (its own origin) is untouched by the truncation.
        assert_eq!(rows[0].agent_link, LinkVerdict::Origin);
    }

    #[test]
    fn a_mid_session_genesis_reads_reseeded_not_broken() {
        let mut w = World::new();
        let a = w.genesis_cell(0x11, 1_000);
        let b = w.genesis_cell(0x22, 0);
        let t1 = w.turn(a, vec![transfer(a, b, 10)]);
        assert!(w.commit_turn(t1).is_committed());
        // A HIRE-shaped out-of-band install: the ledger root moves WITHOUT a
        // turn (the executor-bypassing genesis path, mid-session).
        let _late = w.genesis_cell(0x33, 0);
        let t2 = w.turn(a, vec![transfer(a, b, 20)]);
        assert!(w.commit_turn(t2).is_committed());

        // The recorded History names the boundary: only receipt 1 follows an
        // install (the pre-first-commit installs shape row 0, an origin).
        let flags = reseeded_flags(w.recorded_turns());
        assert_eq!(flags, vec![false, true]);

        // WITHOUT the flags the boundary would read BROKEN (the strictest,
        // history-blind read — a false alarm on a lawful world)…
        let strict = walk_rows(w.receipts(), &[], &[]);
        assert_eq!(strict[1].state_link, LinkVerdict::Broken);
        // …WITH them it is named for what it is, the back-edge still
        // recomputes clean across the boundary, and the chain verifies.
        let rows = walk_rows(w.receipts(), &[], &flags);
        assert_eq!(rows[1].state_link, LinkVerdict::Reseeded);
        assert_eq!(rows[1].agent_link, LinkVerdict::Verified);
        assert!(chain_verifies_to_depth(w.receipts(), &flags, 8));
    }

    #[test]
    fn effects_lines_thread_and_fall_back() {
        let (w, ..) = two_agent_world();
        let lines = vec!["Transfer".to_string(), "Transfer".to_string()];
        let rows = walk_rows(w.receipts(), &lines, &[]);
        assert_eq!(rows[0].effects, "Transfer");
        assert_eq!(rows[1].effects, "Transfer");
        // Past the slice's end: the receipt's own action count, honestly.
        assert_eq!(rows[2].effects, "1 action");
    }
}
