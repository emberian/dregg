//! THE RECEIPT RAIL — make the verified save LAND.
//!
//! Today a receipted save is one status-line string (`N saves · on-ledger`,
//! [`crate::editor::Editor::save`]) while the per-file receipt timeline —
//! [`FirmamentFs::history`](crate::fs::FirmamentFs::history), the ordered
//! `Vec<TurnReceipt>` the spine already attributes per file — is rendered by
//! NOTHING. This module is the missing face: a **rail of chained receipt
//! chips**, one per committed save of the open file, each showing the receipt
//! hash, the rail height, the pre→post state morph, the computron spend, and
//! the chain link back to the previous turn. Saving stops feeling dutiful and
//! starts feeling like minting.
//!
//! ## Two layers, split on the same seam as the rest of the crate
//!
//! * **The model** (this module's top level) — gpui-free, firmament-free pure
//!   logic over [`ReceiptFact`]s: link classification ([`link_kinds`]), rail
//!   verification against the spine's global log ([`verify_rail`]), and the
//!   display helpers ([`short_hex`], [`format_utc`]). Compiles in the
//!   wasm-shaped `--no-default-features` core, so the in-browser editor's
//!   backend can reuse it verbatim. `#[cfg(test)]` tests cover every branch.
//! * **The view** (the `gui`-gated [`ReceiptRail`]) — a [`Render`](gpui::Render)
//!   entity mirroring [`crate::doc_viewer::DocViewer`]'s snapshot discipline:
//!   it holds OWNED `Vec<ReceiptFact>`s (never a borrow on the live spine
//!   across frames) and re-snapshots when the pane refreshes it.
//!
//! ## Why `ReceiptFact` and not `TurnReceipt`
//!
//! The [`Fs`](crate::fs::Fs) seam is compiled with or without the `firmament`
//! feature, so its trait surface cannot name `dregg_turn::TurnReceipt`.
//! `ReceiptFact` is the plain, always-compiled projection of a receipt — the
//! fields the rail renders and verifies — with a `From<&TurnReceipt>` built
//! under `firmament`. The `receipt_hash` field carries the REAL
//! `TurnReceipt::receipt_hash()` computed from the full receipt at projection
//! time; the rail verifies STRUCTURE over those hashes (ordering, linkage,
//! membership in the global log). Full cryptographic re-verification of each
//! receipt is the verifier floor's job, not a UI strip's.
//!
//! ## What "verify" honestly means here
//!
//! The receipt chain is threaded per AGENT across ALL files (the executor
//! chains `previous_receipt_hash` through every turn the editor cell commits),
//! so a file's own timeline is generally NOT a contiguous chain: save a, save
//! b, save a again — a's second receipt links to *b's* hash. The rail therefore
//! verifies the true property: **this file's timeline is an ordered
//! subsequence of the spine's global receipt log**, with each adjacent pair
//! classified [`Direct`](LinkKind::Direct) (no turn intervened) or
//! [`ViaOtherTurns`](LinkKind::ViaOtherTurns) (the chain passed through other
//! saves in between). A spine that publishes no global log (the default
//! [`LedgerSpine::receipts`](crate::fs::firmament) impl) still gets the
//! intra-rail checks; the verdict says so rather than overclaiming.

/// The always-compiled projection of one committed save's `TurnReceipt` — the
/// fields the rail renders and verifies. Built via `From<&TurnReceipt>` under
/// the `firmament` feature; a plain struct here so the [`Fs`](crate::fs::Fs)
/// trait (compiled in the gpui-free, firmament-free core) can speak it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceiptFact {
    /// The receipt's own hash — `TurnReceipt::receipt_hash()`, computed from
    /// the FULL receipt (v3 domain-tagged BLAKE3) at projection time.
    pub receipt_hash: [u8; 32],
    /// The agent's chain link: the hash of the previous receipt this agent
    /// committed (across ALL files), `None` for the agent's first turn.
    pub previous_receipt_hash: Option<[u8; 32]>,
    /// The ledger state commitment BEFORE the save turn.
    pub pre_state_hash: [u8; 32],
    /// The ledger state commitment AFTER — the morph the save landed.
    pub post_state_hash: [u8; 32],
    /// The turn's timestamp (unix seconds; fixtures may stamp 0).
    pub timestamp: i64,
    /// Computrons the turn metered.
    pub computrons_used: u64,
    /// How many actions the turn carried (a save is one `save` action).
    pub action_count: usize,
    /// The agent cell's id bytes (the editor cell — who saved).
    pub agent: [u8; 32],
    /// `true` when the receipt's finality is `Tentative` (solo-mode node,
    /// awaiting quorum) rather than `Final`.
    pub tentative: bool,
}

/// Project a real `TurnReceipt` into the rail's fact shape. The hash is the
/// receipt's own `receipt_hash()` — computed here, once, from the full receipt,
/// so the fact carries the genuine chain identity.
#[cfg(feature = "firmament")]
impl From<&dregg_turn::TurnReceipt> for ReceiptFact {
    fn from(r: &dregg_turn::TurnReceipt) -> Self {
        ReceiptFact {
            receipt_hash: r.receipt_hash(),
            previous_receipt_hash: r.previous_receipt_hash,
            pre_state_hash: r.pre_state_hash,
            post_state_hash: r.post_state_hash,
            timestamp: r.timestamp,
            computrons_used: r.computrons_used,
            action_count: r.action_count,
            agent: r.agent.0,
            tentative: matches!(r.finality, dregg_turn::Finality::Tentative),
        }
    }
}

/// How one rail chip connects to the chip before it (see [`link_kinds`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LinkKind {
    /// The FIRST chip on this rail — nothing before it *on this file*. Its
    /// `previous_receipt_hash` may still be `Some` (an earlier turn on another
    /// file); that is the agent's chain, not this rail's.
    RailGenesis,
    /// `previous_receipt_hash` IS the previous rail chip's hash — no other
    /// turn intervened between the two saves of this file.
    Direct,
    /// The agent's chain passed through OTHER turns (saves of other files)
    /// between this chip and the previous one. Normal, not suspicious — the
    /// chain is global; [`verify_rail`] checks the subsequence embedding.
    ViaOtherTurns,
}

/// Classify each chip's link to its predecessor, in rail (commit) order.
/// `kinds[0]` is always [`LinkKind::RailGenesis`]; empty rail → empty vec.
pub fn link_kinds(rail: &[ReceiptFact]) -> Vec<LinkKind> {
    rail.iter()
        .enumerate()
        .map(|(i, fact)| {
            if i == 0 {
                LinkKind::RailGenesis
            } else if fact.previous_receipt_hash == Some(rail[i - 1].receipt_hash) {
                LinkKind::Direct
            } else {
                LinkKind::ViaOtherTurns
            }
        })
        .collect()
}

/// The outcome of [`verify_rail`] — what the ✓/✗ badge states.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RailVerdict {
    /// No chips to verify (a seed is genesis, not a turn — no receipt yet).
    Empty,
    /// Every check passed. `direct`/`threaded` count the adjacent links by
    /// kind (the rail-genesis chip is neither); `global_checked` is `true`
    /// when the spine published a global log and the rail verified as an
    /// ordered subsequence of it — `false` means the spine publishes no
    /// global log, so only the intra-rail checks ran (said, not overclaimed).
    Verified {
        direct: usize,
        threaded: usize,
        global_checked: bool,
    },
    /// A check failed at rail index `at` (0-based). `reason` is the in-band
    /// human sentence for the badge/tooltip.
    Broken { at: usize, reason: String },
}

/// Whether `facts` form ONE contiguous receipt chain end-to-end (each entry's
/// `previous_receipt_hash` is exactly the previous entry's hash). True for a
/// single-agent spine's global log (the OwnedSpine shape); a multi-agent
/// World's log interleaves several agents' chains and won't be.
pub fn is_connected_chain(facts: &[ReceiptFact]) -> bool {
    facts
        .windows(2)
        .all(|w| w[1].previous_receipt_hash == Some(w[0].receipt_hash))
}

/// **Verify the rail** — the ✓-button's whole job, pure and testable:
///
/// 1. no duplicate receipt hashes on the rail (a replayed chip is a lie);
/// 2. timestamps non-decreasing in rail order (commit order is time order);
/// 3. when `global` is non-empty: the rail is an ordered subsequence of the
///    global log, and each matched entry is FIELD-IDENTICAL (a rail chip that
///    disagrees with the log's copy of the same hash is tampered);
/// 4. adjacent links classified ([`link_kinds`]) and counted.
///
/// `global` may be empty (a spine that doesn't publish its log) — the verdict
/// then carries `global_checked: false` instead of pretending.
pub fn verify_rail(rail: &[ReceiptFact], global: &[ReceiptFact]) -> RailVerdict {
    if rail.is_empty() {
        return RailVerdict::Empty;
    }

    // 1. Duplicates.
    for (i, fact) in rail.iter().enumerate() {
        if rail[..i]
            .iter()
            .any(|f| f.receipt_hash == fact.receipt_hash)
        {
            return RailVerdict::Broken {
                at: i,
                reason: format!(
                    "chip #{h} repeats receipt {hash} already on the rail",
                    h = i + 1,
                    hash = short_hex(&fact.receipt_hash, 4)
                ),
            };
        }
    }

    // 2. Time order.
    for i in 1..rail.len() {
        if rail[i].timestamp < rail[i - 1].timestamp {
            return RailVerdict::Broken {
                at: i,
                reason: format!(
                    "chip #{h} is timestamped before its predecessor ({} < {})",
                    rail[i].timestamp,
                    rail[i - 1].timestamp,
                    h = i + 1,
                ),
            };
        }
    }

    // 3. Ordered-subsequence embedding in the global log (when published).
    let global_checked = !global.is_empty();
    if global_checked {
        let mut cursor = 0usize;
        for (i, fact) in rail.iter().enumerate() {
            let found = global[cursor..]
                .iter()
                .position(|g| g.receipt_hash == fact.receipt_hash);
            match found {
                Some(off) => {
                    let g = &global[cursor + off];
                    if g != fact {
                        return RailVerdict::Broken {
                            at: i,
                            reason: format!(
                                "chip #{h} ({hash}) disagrees with the global log's copy \
                                 of the same receipt",
                                h = i + 1,
                                hash = short_hex(&fact.receipt_hash, 4)
                            ),
                        };
                    }
                    cursor += off + 1;
                }
                None => {
                    return RailVerdict::Broken {
                        at: i,
                        reason: format!(
                            "chip #{h} ({hash}) is not in the global receipt log \
                             (or is out of commit order)",
                            h = i + 1,
                            hash = short_hex(&fact.receipt_hash, 4)
                        ),
                    };
                }
            }
        }
    }

    // 4. Link census.
    let kinds = link_kinds(rail);
    let direct = kinds.iter().filter(|k| **k == LinkKind::Direct).count();
    let threaded = kinds
        .iter()
        .filter(|k| **k == LinkKind::ViaOtherTurns)
        .count();
    RailVerdict::Verified {
        direct,
        threaded,
        global_checked,
    }
}

/// The first `n` bytes of a hash as lowercase hex — the chip fingerprint
/// (`n = 4` → the 8-hex form the pitch names).
pub fn short_hex(bytes: &[u8; 32], n: usize) -> String {
    bytes
        .iter()
        .take(n.min(32))
        .map(|b| format!("{b:02x}"))
        .collect()
}

/// Unix seconds → `YYYY-MM-DD HH:MM:SS UTC`, no chrono dep (Hinnant's
/// `civil_from_days`, the standard 20-line proleptic-Gregorian inverse).
/// Non-positive stamps (fixtures/tests often stamp 0) render as the raw
/// `t=<n>` so a zero never masquerades as the epoch date meaning something.
pub fn format_utc(ts: i64) -> String {
    if ts <= 0 {
        return format!("t={ts}");
    }
    let days = ts.div_euclid(86_400);
    let secs = ts.rem_euclid(86_400);
    let (y, m, d) = civil_from_days(days);
    format!(
        "{y:04}-{m:02}-{d:02} {:02}:{:02}:{:02} UTC",
        secs / 3600,
        (secs / 60) % 60,
        secs % 60
    )
}

/// Days since 1970-01-01 → (year, month, day) proleptic Gregorian.
fn civil_from_days(z: i64) -> (i64, u32, u32) {
    let z = z + 719_468;
    let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
    let doe = (z - era * 146_097) as u64;
    let yoe = (doe - doe / 1_460 + doe / 36_524 - doe / 146_096) / 365;
    let y = yoe as i64 + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = (doy - (153 * mp + 2) / 5 + 1) as u32;
    let m = if mp < 10 { mp + 3 } else { mp - 9 } as u32;
    (if m <= 2 { y + 1 } else { y }, m, d)
}

// --- the view ---------------------------------------------------------------

#[cfg(feature = "gui")]
mod view {
    use gpui::{
        div, px, App, Context, FocusHandle, Focusable, InteractiveElement as _, IntoElement,
        ParentElement as _, Render, SharedString, StatefulInteractiveElement as _, Styled as _,
        Window,
    };
    use gpui_component::{h_flex, v_flex, ActiveTheme as _, StyledExt as _};

    use super::{
        format_utc, link_kinds, short_hex, verify_rail, LinkKind, RailVerdict, ReceiptFact,
    };

    /// The per-file receipt timeline pane: one chip per committed save of the
    /// open file, newest on top, plus a ✓ verify-chain action. Snapshot-owning
    /// (mirrors [`crate::doc_viewer::DocViewer`]): it holds owned fact vecs so
    /// it renders across frames without borrowing the live spine; the editor
    /// pane re-snapshots it via [`ReceiptRail::set_snapshot`] whenever the
    /// editor notifies (open, save, merge).
    pub struct ReceiptRail {
        /// This file's receipts, in commit order (oldest first — chip #1 is
        /// `facts[0]`; the render walks it newest-first).
        facts: Vec<ReceiptFact>,
        /// The spine's global receipt log (for [`verify_rail`]'s subsequence
        /// embedding). Empty when the spine publishes none.
        global: Vec<ReceiptFact>,
        /// The open document's title (filename), for the header.
        title: SharedString,
        /// The last verify outcome — `None` until the ✓ button runs (and
        /// cleared by every re-snapshot, so a stale verdict never describes a
        /// newer rail).
        verdict: Option<RailVerdict>,
        focus: FocusHandle,
    }

    impl ReceiptRail {
        /// An empty rail (no file open / no saves yet).
        pub fn new(cx: &mut App) -> Self {
            Self {
                facts: Vec::new(),
                global: Vec::new(),
                title: SharedString::from("no document"),
                verdict: None,
                focus: cx.focus_handle(),
            }
        }

        /// Replace the snapshot: this file's timeline + the spine's global log
        /// + the document title. Clears any cached verdict (it described the
        /// OLD rail; the ✓ button re-verifies the new one on demand).
        pub fn set_snapshot(
            &mut self,
            facts: Vec<ReceiptFact>,
            global: Vec<ReceiptFact>,
            title: impl Into<SharedString>,
        ) {
            self.facts = facts;
            self.global = global;
            self.title = title.into();
            self.verdict = None;
        }

        /// How many chips the rail carries (this file's committed-save count).
        pub fn chip_count(&self) -> usize {
            self.facts.len()
        }

        /// The newest chip's receipt hash, if any save has landed.
        pub fn latest_hash(&self) -> Option<[u8; 32]> {
            self.facts.last().map(|f| f.receipt_hash)
        }

        /// Run the verification (the ✓ button's host path) and cache + return
        /// the verdict. Pure over the snapshot — see [`verify_rail`].
        pub fn run_verify(&mut self) -> &RailVerdict {
            self.verdict = Some(verify_rail(&self.facts, &self.global));
            self.verdict.as_ref().expect("just set")
        }

        /// The cached verdict, if the ✓ button has run since the last snapshot.
        pub fn verdict(&self) -> Option<&RailVerdict> {
            self.verdict.as_ref()
        }

        /// The verdict badge (right of the header): grey until verified, green
        /// on ✓, red with the in-band reason on ✗.
        fn verdict_badge(&self, cx: &App) -> impl IntoElement {
            let theme = cx.theme();
            let (bg, fg, label) = match &self.verdict {
                None => (
                    theme.secondary,
                    theme.muted_foreground,
                    "unverified".to_string(),
                ),
                Some(RailVerdict::Empty) => (
                    theme.secondary,
                    theme.muted_foreground,
                    "nothing to verify".to_string(),
                ),
                Some(RailVerdict::Verified {
                    direct,
                    threaded,
                    global_checked,
                }) => (
                    theme.success,
                    theme.success_foreground,
                    format!(
                        "✓ verified — {direct} direct · {threaded} threaded{}",
                        if *global_checked {
                            " · in the global log"
                        } else {
                            " · no global log published"
                        }
                    ),
                ),
                Some(RailVerdict::Broken { at, reason }) => (
                    theme.danger,
                    theme.danger_foreground,
                    format!("✗ broken at chip #{}: {reason}", at + 1),
                ),
            };
            div()
                .px_2()
                .py_0p5()
                .rounded_sm()
                .bg(bg)
                .text_xs()
                .text_color(fg)
                .child(SharedString::from(label))
        }

        /// One receipt chip: height badge, 8-hex receipt hash, chain link to
        /// the predecessor, pre→post state morph, computrons, action count,
        /// timestamp. `height` is 1-based commit order; `latest` accents the
        /// chip a fresh save just minted.
        fn chip(
            &self,
            fact: &ReceiptFact,
            height: usize,
            kind: LinkKind,
            latest: bool,
            cx: &App,
        ) -> impl IntoElement {
            let theme = cx.theme();
            let accent = if latest { theme.blue } else { theme.border };

            // The chain-link line: how this chip connects backwards.
            let link = match (kind, fact.previous_receipt_hash) {
                (LinkKind::RailGenesis, None) => {
                    "⛓ chain genesis — the agent's first turn".to_string()
                }
                (LinkKind::RailGenesis, Some(prev)) => format!(
                    "⛓ ← {} (an earlier turn, before this file's first save)",
                    short_hex(&prev, 4)
                ),
                (LinkKind::Direct, Some(prev)) => {
                    format!("⛓ ← {} · direct", short_hex(&prev, 4))
                }
                (LinkKind::ViaOtherTurns, Some(prev)) => {
                    format!("⛓ ‥ {} · via other turns", short_hex(&prev, 4))
                }
                // A non-genesis chip with no prev hash — render honestly; the
                // ✓ verify treats ordering/membership, not this display arm.
                (_, None) => "⛓ (no previous-receipt link)".to_string(),
            };

            let morph = format!(
                "{} → {}",
                short_hex(&fact.pre_state_hash, 4),
                short_hex(&fact.post_state_hash, 4)
            );
            let meter = format!(
                "⚙ {} computrons · {} action{}{}",
                fact.computrons_used,
                fact.action_count,
                if fact.action_count == 1 { "" } else { "s" },
                if fact.tentative { " · tentative" } else { "" }
            );

            h_flex()
                .w_full()
                .gap_2()
                .p_2()
                .my_0p5()
                .rounded_md()
                .border_1()
                .border_color(accent)
                .bg(theme.secondary)
                .items_start()
                // Height badge — the rail coordinate.
                .child(
                    div()
                        .px_2()
                        .py_0p5()
                        .rounded_sm()
                        .bg(if latest { theme.blue } else { theme.background })
                        .text_xs()
                        .font_semibold()
                        .text_color(if latest {
                            theme.background
                        } else {
                            theme.muted_foreground
                        })
                        .child(SharedString::from(format!("#{height}"))),
                )
                .child(
                    v_flex()
                        .flex_1()
                        .gap_0p5()
                        .child(
                            h_flex()
                                .gap_2()
                                .items_center()
                                .child(
                                    div()
                                        .text_sm()
                                        .font_semibold()
                                        .font_family("monospace")
                                        .text_color(theme.foreground)
                                        .child(SharedString::from(short_hex(
                                            &fact.receipt_hash,
                                            4,
                                        ))),
                                )
                                .child(
                                    div()
                                        .text_xs()
                                        .text_color(theme.muted_foreground)
                                        .child(SharedString::from(format_utc(fact.timestamp))),
                                )
                                .child(div().flex_1())
                                .child(
                                    div()
                                        .text_xs()
                                        .font_family("monospace")
                                        .text_color(theme.muted_foreground)
                                        .child(SharedString::from(morph)),
                                ),
                        )
                        .child(
                            div()
                                .text_xs()
                                .font_family("monospace")
                                .text_color(theme.muted_foreground)
                                .child(SharedString::from(link)),
                        )
                        .child(
                            div()
                                .text_xs()
                                .text_color(theme.muted_foreground)
                                .child(SharedString::from(meter)),
                        ),
                )
        }
    }

    impl Focusable for ReceiptRail {
        fn focus_handle(&self, _cx: &App) -> FocusHandle {
            self.focus.clone()
        }
    }

    impl Render for ReceiptRail {
        fn render(&mut self, _window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
            let theme = cx.theme();

            let verify_button = div()
                .id("receipt-rail-verify")
                .px_3()
                .py_0p5()
                .cursor_pointer()
                .rounded_sm()
                .border_1()
                .border_color(theme.border)
                .bg(theme.background)
                .text_xs()
                .text_color(theme.foreground)
                .child(SharedString::from("⛓ verify chain"))
                .on_click(cx.listener(|this, _ev, _window, cx| {
                    this.run_verify();
                    cx.notify();
                }));

            let header = h_flex()
                .w_full()
                .px_2()
                .py_1()
                .gap_2()
                .items_center()
                .bg(theme.secondary)
                .border_b_1()
                .border_color(theme.border)
                .child(
                    div()
                        .font_semibold()
                        .text_sm()
                        .text_color(theme.foreground)
                        .child(self.title.clone()),
                )
                .child(div().text_xs().text_color(theme.muted_foreground).child(
                    SharedString::from(format!(
                        "{} receipted save{} · this file",
                        self.facts.len(),
                        if self.facts.len() == 1 { "" } else { "s" }
                    )),
                ))
                .child(div().flex_1())
                .child(verify_button)
                .child(self.verdict_badge(cx));

            // Chips newest-first: a fresh Cmd-S lands its chip on TOP.
            let kinds = link_kinds(&self.facts);
            let last = self.facts.len().saturating_sub(1);
            let mut body = v_flex().w_full().gap_0().p_1();
            if self.facts.is_empty() {
                body = body.child(
                    div()
                        .p_2()
                        .text_sm()
                        .text_color(theme.muted_foreground)
                        .child(SharedString::from(
                            "no receipted saves yet — a seed is genesis, not a turn; \
                             the first save mints the first chip",
                        )),
                );
            } else {
                for (i, fact) in self.facts.iter().enumerate().rev() {
                    body = body.child(self.chip(fact, i + 1, kinds[i], i == last, cx));
                }
            }

            v_flex()
                .size_full()
                .bg(theme.background)
                .track_focus(&self.focus)
                .child(header)
                .child(div().flex_1().min_h(px(0.)).overflow_hidden().child(body))
        }
    }
}

#[cfg(feature = "gui")]
pub use view::ReceiptRail;

#[cfg(test)]
mod tests {
    use super::*;

    /// A synthetic fact: hash = `[id; 32]`, prev = `Some([prev; 32])` (or None).
    fn fact(id: u8, prev: Option<u8>, ts: i64) -> ReceiptFact {
        ReceiptFact {
            receipt_hash: [id; 32],
            previous_receipt_hash: prev.map(|p| [p; 32]),
            pre_state_hash: [0xAA; 32],
            post_state_hash: [0xBB; 32],
            timestamp: ts,
            computrons_used: 7,
            action_count: 1,
            agent: [0xED; 32],
            tentative: false,
        }
    }

    #[test]
    fn empty_rail_verdict_is_empty() {
        assert_eq!(verify_rail(&[], &[]), RailVerdict::Empty);
        assert!(link_kinds(&[]).is_empty());
    }

    #[test]
    fn directly_chained_rail_verifies() {
        // Two saves of one file, nothing between them: chip 2 links chip 1.
        let rail = vec![fact(1, None, 10), fact(2, Some(1), 11)];
        let kinds = link_kinds(&rail);
        assert_eq!(kinds, vec![LinkKind::RailGenesis, LinkKind::Direct]);
        assert_eq!(
            verify_rail(&rail, &rail),
            RailVerdict::Verified {
                direct: 1,
                threaded: 0,
                global_checked: true
            }
        );
    }

    #[test]
    fn interleaved_saves_thread_through_the_global_chain() {
        // save a (1), save b (2), save a (3): a's rail is [1, 3]; 3 links to 2
        // (the b save) — ViaOtherTurns, and the rail embeds in the global log.
        let a1 = fact(1, None, 10);
        let b = fact(2, Some(1), 11);
        let a2 = fact(3, Some(2), 12);
        let rail = vec![a1.clone(), a2.clone()];
        let global = vec![a1, b, a2];
        assert!(is_connected_chain(&global));
        assert_eq!(
            link_kinds(&rail),
            vec![LinkKind::RailGenesis, LinkKind::ViaOtherTurns]
        );
        assert_eq!(
            verify_rail(&rail, &global),
            RailVerdict::Verified {
                direct: 0,
                threaded: 1,
                global_checked: true
            }
        );
    }

    #[test]
    fn a_rail_chip_absent_from_the_global_log_is_broken() {
        let rail = vec![fact(1, None, 10), fact(9, Some(1), 11)];
        let global = vec![fact(1, None, 10), fact(2, Some(1), 11)];
        match verify_rail(&rail, &global) {
            RailVerdict::Broken { at, reason } => {
                assert_eq!(at, 1);
                assert!(reason.contains("not in the global receipt log"), "{reason}");
            }
            other => panic!("expected Broken, got {other:?}"),
        }
    }

    #[test]
    fn out_of_commit_order_embedding_is_broken() {
        // The rail claims [2, 1] but the global log committed 1 before 2 — the
        // subsequence cursor cannot find 1 after 2.
        let g1 = fact(1, None, 10);
        let g2 = fact(2, Some(1), 10);
        let rail = vec![g2.clone(), g1.clone()];
        let global = vec![g1, g2];
        assert!(matches!(
            verify_rail(&rail, &global),
            RailVerdict::Broken { at: 1, .. }
        ));
    }

    #[test]
    fn a_tampered_chip_disagreeing_with_the_log_is_broken() {
        // Same hash, different metered computrons: the rail's copy is not the
        // log's copy — field-identity is part of the embedding check.
        let real = fact(1, None, 10);
        let mut forged = real.clone();
        forged.computrons_used = 999_999;
        match verify_rail(&[forged], &[real]) {
            RailVerdict::Broken { at: 0, reason } => {
                assert!(reason.contains("disagrees"), "{reason}");
            }
            other => panic!("expected Broken, got {other:?}"),
        }
    }

    #[test]
    fn duplicate_chips_are_broken() {
        let rail = vec![fact(1, None, 10), fact(1, None, 10)];
        assert!(matches!(
            verify_rail(&rail, &[]),
            RailVerdict::Broken { at: 1, .. }
        ));
    }

    #[test]
    fn time_regression_is_broken() {
        let rail = vec![fact(1, None, 10), fact(2, Some(1), 9)];
        match verify_rail(&rail, &[]) {
            RailVerdict::Broken { at: 1, reason } => {
                assert!(reason.contains("timestamped before"), "{reason}");
            }
            other => panic!("expected Broken, got {other:?}"),
        }
    }

    #[test]
    fn no_global_log_still_verifies_intra_rail_but_says_so() {
        let rail = vec![fact(1, None, 10), fact(2, Some(1), 11)];
        assert_eq!(
            verify_rail(&rail, &[]),
            RailVerdict::Verified {
                direct: 1,
                threaded: 0,
                global_checked: false
            }
        );
    }

    #[test]
    fn short_hex_is_the_8_hex_fingerprint() {
        let mut h = [0u8; 32];
        h[0] = 0xa1;
        h[1] = 0xb2;
        h[2] = 0xc3;
        h[3] = 0xd4;
        assert_eq!(short_hex(&h, 4), "a1b2c3d4");
        assert_eq!(short_hex(&h, 0), "");
    }

    #[test]
    fn format_utc_renders_civil_dates_and_raw_nonpositive() {
        assert_eq!(format_utc(0), "t=0");
        assert_eq!(format_utc(-5), "t=-5");
        assert_eq!(format_utc(86_399), "1970-01-01 23:59:59 UTC");
        // 2000-02-29 (leap day): 946684800 (y2k) + 31d Jan + 28d Feb.
        assert_eq!(format_utc(951_782_400), "2000-02-29 00:00:00 UTC");
    }

    /// LIVE-SPINE grounding (firmament builds): the facts projected from a real
    /// `FirmamentFs` rail verify against its real global log, with the exact
    /// interleaving shape `per_file_history_is_attributed_and_ordered` proves
    /// at the receipt layer.
    #[cfg(feature = "firmament")]
    #[test]
    fn live_firmament_rail_projects_and_verifies() {
        use crate::fs::{FirmamentFs, Fs as _};
        use std::path::PathBuf;

        let fs = FirmamentFs::new();
        let a = PathBuf::from("/proj/a.rs");
        let b = PathBuf::from("/proj/b.rs");
        fs.seed_file(&a, "a0").unwrap();
        fs.seed_file(&b, "b0").unwrap();

        // A seed is genesis — the rail is empty and verifies Empty.
        assert!(fs.receipt_facts_for(&a).is_empty());
        assert_eq!(
            verify_rail(&fs.receipt_facts_for(&a), &fs.receipt_facts()),
            RailVerdict::Empty
        );

        // Interleave saves (a, b, a), then one more direct save of a.
        fs.save(&a, "a1").unwrap();
        fs.save(&b, "b1").unwrap();
        fs.save(&a, "a2").unwrap();
        fs.save(&a, "a3").unwrap();

        let rail = fs.receipt_facts_for(&a);
        let global = fs.receipt_facts();
        assert_eq!(rail.len(), 3, "three saves of a");
        assert_eq!(global.len(), 4, "four turns total");
        assert_eq!(
            link_kinds(&rail),
            vec![
                LinkKind::RailGenesis,
                LinkKind::ViaOtherTurns, // the b save intervened
                LinkKind::Direct,        // a3 right after a2
            ]
        );
        assert_eq!(
            verify_rail(&rail, &global),
            RailVerdict::Verified {
                direct: 1,
                threaded: 1,
                global_checked: true
            }
        );

        // The newest chip is the fs's own last receipt — one truth, two reads.
        assert_eq!(
            rail.last().map(|f| f.receipt_hash),
            fs.last_save_receipt_hash()
        );

        // The single-agent owned spine's global log is one connected chain.
        assert!(is_connected_chain(&global));
    }
}
