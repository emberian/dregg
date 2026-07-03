//! **The SPOTTER** — a Pharo-style fuzzy command palette for the deos desktop.
//!
//! Pharo's Spotter is the single keystroke that ties every surface together: you
//! summon a floating overlay, type anything, and jump — to a CELL (by id-prefix or
//! kind), to an ACTION on that cell (open as document, explore, inspect, links,
//! transcript, workflow), or to an open WINDOW. It produces a ranked list of
//! candidate entries; selecting one dispatches the corresponding desktop gesture.
//!
//! ## The clobber-safe split
//!
//! This module owns the DATA MODEL ([`SpotterTarget`], [`SpotterEntry`]), the pure
//! [`rank`] scorer (the load-bearing, unit-testable core), the [`candidates_for_cells`]
//! builder, and a pure [`render_spotter_rows`] presentation fn that returns inert
//! result rows. The desktop View (`DeosDesktop`) owns the text input, the open-windows
//! map, the `cx.listener` click/arrow wiring, and the actual dispatch of a selected
//! [`SpotterTarget`]. The fuzzy match and scoring are gpui-free, so they compile and
//! test without a renderer.

use gpui::prelude::FluentBuilder;
use gpui::{div, px, AnyElement, FontWeight, IntoElement, ParentElement, Styled};

use dregg_types::CellId;

use crate::deos_desktop::chrome::{
    bevel_raised, id_short, NT_DIM, NT_FACE_DARK, NT_SELECT, NT_TEXT, NT_TITLE_TEXT,
};

// ── The candidate model ───────────────────────────────────────────────────────────

/// The gesture a selected spotter entry dispatches. The desktop View matches on this
/// to open the corresponding window kind (or focus the cell), each over the named
/// cell. One cell yields a `Cell` entry plus the full action vocabulary; the GLOBAL
/// surface variants ([`WorldExplorer`](Self::WorldExplorer) …) carry no cell — they
/// jump to a place, not a cell, so the Spotter is the ONE entry to every surface.
#[derive(Clone)]
pub enum SpotterTarget {
    /// Focus / inspect the cell (the bare jump-to-cell).
    Cell(CellId),
    /// Open the cell as a document editor.
    OpenDoc(CellId),
    /// Open the Document Explorer (history · graph · blame) over the cell.
    Explore(CellId),
    /// Open the reflective inspector window on the cell.
    Inspect(CellId),
    /// Open the links / backlinks view over the cell.
    Links(CellId),
    /// Open the transcript / receipt-log window.
    Transcript(CellId),
    /// Open the workflow-composer window over the cell.
    Workflow(CellId),
    /// Open the World Explorer — the map of everything (ledger · chronicle · Σ=0). A
    /// global surface: anchored on the desktop's user sentinel by the dispatcher.
    WorldExplorer,
    /// Open the AGENT ROOM — the resident's provable activity (receipted actions ·
    /// held mandate · authorization boundary). A global surface: anchored on the
    /// room's own sentinel cell by the dispatcher.
    AgentRoom,
    /// Open the World Transcript — the receipt log of every committed turn (global).
    WorldTranscript,
    /// Open a DOCUMENT-COLLABORATION session — a document editor over the user's own
    /// cell with a forked co-author draft already in flight, ready to diverge · stitch ·
    /// resolve (the branch-and-stitch flow as ONE reachable place, not a button you must
    /// first discover inside an editor). A global surface, anchored on the user sentinel.
    DocCollab,
    /// Open the WORLD-STATUS BOARD — a `deos_view::ViewNode` rendered through deos-view's
    /// native renderer, beside the native chrome (global). This is the agent-composable
    /// reflective surface (a confined agent reflects-on + rewrites it, and composes new
    /// boards OF it). Gated on the `card-pane` feature that compiles the content-IR pane in.
    #[cfg(feature = "card-pane")]
    PortableCard,
    /// Open the DISCORD-BOT SURFACE — the desktop face of the one dregg-driven bot: a
    /// `deos_view::ViewNode` card that drives the bot's ops as dregg turns and renders
    /// the bot's activity feed (the SAME card the bot renders as a Discord embed). A
    /// global surface, anchored on the bot-surface window cell. Gated on `card-pane`.
    #[cfg(feature = "card-pane")]
    BotSurface,
    /// Open a confined ANDROID CELL dressed as the phone's SystemUI cap-chrome — the
    /// status bar · the pull-down quick-settings shade · the hand-over sheet (a tap is a
    /// real `Effect::GrantCapability` on the confined ledger). A global surface, anchored
    /// on the user sentinel. Gated on `android-systemui` (where the cap-chrome is in scope).
    #[cfg(feature = "android-systemui")]
    AndroidCell,
    /// Open the APP SHELF — the roster of pre-built starbridge-apps as first-class
    /// desktop citizens (launch one and its cell + receipt land on the LIVE World). A
    /// global surface, anchored on the user sentinel. Gated on `app-registry` (where
    /// the registry + the app crates are in scope); the candidates come from
    /// [`crate::deos_desktop::app_shelf::app_spotter_candidates`].
    #[cfg(feature = "app-registry")]
    AppShelf,
    /// LAUNCH the named registry app straight from the palette — the dispatcher runs
    /// the SAME `launch_on_world` flow the shelf's button does (a real verified turn;
    /// the app's cell becomes a desktop icon). Carries the registry id (`&'static`
    /// because every [`crate::app_registry::AppEntry::id`] is). Gated on `app-registry`.
    #[cfg(feature = "app-registry")]
    LaunchApp(&'static str),
    /// Open the EXCHANGE FLOOR — the $DREGG agent-economy window (offers as live
    /// cells; post → lease → settle each a real verified turn; Σδ=0 settlement; the
    /// over-budget cheat refused by the executor). A global surface, anchored on the
    /// user sentinel. Gated on `app-registry` (the compute-exchange /
    /// execution-lease substrate crates in scope); the candidate comes from
    /// [`crate::deos_desktop::exchange_floor::exchange_spotter_candidates`].
    #[cfg(feature = "app-registry")]
    ExchangeFloor,
}

/// One ranked candidate in the spotter result list. `label` is the reader-legible
/// primary line, `sublabel` the dim secondary line, `target` the gesture to dispatch,
/// and `score` the fuzzy-match quality (higher = better) used to sort the results.
#[derive(Clone)]
pub struct SpotterEntry {
    /// The reader-legible primary line, e.g. "Inspect  account 1a2b3c4d".
    pub label: String,
    /// The dim secondary line, e.g. "cell · balance 1,000 · Live" or "action".
    pub sublabel: String,
    /// The gesture this entry dispatches when selected.
    pub target: SpotterTarget,
    /// The match quality (higher = better) — the sort key.
    pub score: i64,
}

// ── The ranking — the pure, load-bearing core ─────────────────────────────────────

/// Rank `candidates` against `query` by a case-insensitive SUBSEQUENCE fuzzy match of
/// `query` against each entry's `label` (the classic spotter match: the chars of the
/// query appear, in order, somewhere in the label).
///
/// An empty query returns every candidate in input order (a reasonable default list).
/// A query that does not subsequence-match a label drops that entry. The surviving
/// entries are returned sorted by score descending; ties keep input order (a stable
/// sort), so a stable presentation falls out for equal-quality matches.
///
/// The score (see [`score_match`]) rewards a contiguous run, a match landing at a
/// word start, an earlier first match, and a shorter label.
pub fn rank(query: &str, candidates: &[SpotterEntry]) -> Vec<SpotterEntry> {
    if query.trim().is_empty() {
        return candidates.to_vec();
    }
    let q: Vec<char> = query
        .to_lowercase()
        .chars()
        .filter(|c| !c.is_whitespace())
        .collect();
    if q.is_empty() {
        return candidates.to_vec();
    }
    let mut scored: Vec<SpotterEntry> = candidates
        .iter()
        .filter_map(|e| {
            score_match(&q, &e.label).map(|s| SpotterEntry {
                score: s,
                ..e.clone()
            })
        })
        .collect();
    // Sort by score descending; `sort_by` is stable, so equal scores keep input order.
    scored.sort_by_key(|b| std::cmp::Reverse(b.score));
    scored
}

/// Score the subsequence match of the (already lowercased, whitespace-stripped) query
/// chars `q` against `label`. Returns `None` when `q` is not a subsequence of `label`.
///
/// Scoring rule: walk `label` left to right, advancing through `q` greedily. Each
/// matched query char earns a base point; a match that immediately follows the prior
/// match (a contiguous run) earns a contiguity bonus; a match landing at a word start
/// (label start, or just after a separator) earns a word-start bonus. The whole match
/// then gains an earlier-first-match bonus (the first match nearer the label head
/// scores higher) and a shorter-label bonus (a tighter label outranks a sprawling one
/// for the same query). The result is positive whenever the query matches.
fn score_match(q: &[char], label: &str) -> Option<i64> {
    let hay: Vec<char> = label.to_lowercase().chars().collect();
    if q.is_empty() {
        return Some(0);
    }
    let mut qi = 0usize;
    let mut score: i64 = 0;
    let mut first_match: Option<usize> = None;
    let mut prev_match: Option<usize> = None;
    for (hi, &hc) in hay.iter().enumerate() {
        if qi >= q.len() {
            break;
        }
        if hc == q[qi] {
            score += 8; // base point per matched query char
            if first_match.is_none() {
                first_match = Some(hi);
            }
            // Contiguity: this match directly follows the previous one.
            if let Some(p) = prev_match {
                if hi == p + 1 {
                    score += 12;
                }
            }
            // Word start: label head, or just after a non-alphanumeric separator.
            let at_word_start = hi == 0
                || hay
                    .get(hi.wrapping_sub(1))
                    .map(|c| !c.is_alphanumeric())
                    .unwrap_or(false);
            if at_word_start {
                score += 10;
            }
            prev_match = Some(hi);
            qi += 1;
        }
    }
    if qi < q.len() {
        return None; // query is not a subsequence of the label
    }
    // Earlier first match ranks higher (penalize a late initial hit).
    if let Some(f) = first_match {
        score -= f as i64;
    }
    // Shorter label ranks higher for the same query (a tighter target wins).
    score -= hay.len() as i64 / 4;
    Some(score)
}

// ── The candidate builder ─────────────────────────────────────────────────────────

/// Build the spotter candidate set from the World's cells. For each cell this emits a
/// jump-to-cell entry plus the full action vocabulary (inspect · open as document ·
/// explore · links · transcript · workflow), with labels and sublabels matched to the
/// desktop's right-click-menu wording.
///
/// `face` returns `(kind, detail)` per cell, where `kind` is the cell's short kind
/// label (e.g. "account") and `detail` is the dense status line (e.g.
/// "balance 1,000 · Live"). The desktop reads these off the live ledger each time the
/// query changes and passes them in, keeping this builder ledger-free and testable.
pub fn candidates_for_cells(
    cells: &[CellId],
    face: impl Fn(&CellId) -> (String, String),
) -> Vec<SpotterEntry> {
    let mut out = Vec::with_capacity(cells.len() * 7);
    for cell in cells {
        let (kind, detail) = face(cell);
        let short = id_short(cell);
        let cell_sub = format!("cell · {detail}");

        // The bare jump-to-cell entry.
        out.push(SpotterEntry {
            label: format!("{kind} {short}"),
            sublabel: cell_sub.clone(),
            target: SpotterTarget::Cell(*cell),
            score: 0,
        });
        // The action vocabulary — verbs matched to the desktop context menu.
        let action_sub = format!("action · {kind} {short}");
        out.push(SpotterEntry {
            label: format!("Inspect  {kind} {short}"),
            sublabel: action_sub.clone(),
            target: SpotterTarget::Inspect(*cell),
            score: 0,
        });
        out.push(SpotterEntry {
            label: format!("Open as Document  {kind} {short}"),
            sublabel: action_sub.clone(),
            target: SpotterTarget::OpenDoc(*cell),
            score: 0,
        });
        out.push(SpotterEntry {
            label: format!("Explore Document  {kind} {short}"),
            sublabel: format!("action · history · graph · blame · {kind} {short}"),
            target: SpotterTarget::Explore(*cell),
            score: 0,
        });
        out.push(SpotterEntry {
            label: format!("Links & Backlinks  {kind} {short}"),
            sublabel: action_sub.clone(),
            target: SpotterTarget::Links(*cell),
            score: 0,
        });
        out.push(SpotterEntry {
            label: format!("Transcript  {kind} {short}"),
            sublabel: action_sub.clone(),
            target: SpotterTarget::Transcript(*cell),
            score: 0,
        });
        out.push(SpotterEntry {
            label: format!("Compose Workflow  {kind} {short}"),
            sublabel: format!("action · intents + refinement · {kind} {short}"),
            target: SpotterTarget::Workflow(*cell),
            score: 0,
        });
    }
    out
}

/// Build the GLOBAL surface candidates — the Spotter's jump-to-a-place entries that
/// are not tied to one cell: the World Explorer, the World Transcript, and (when the
/// content-IR pane is compiled in) the Portable-IR card. These are PREPENDED to the
/// per-cell vocabulary so a stranger who opens the Spotter and types nothing sees the
/// whole rooms of the desktop first — the Spotter is the ONE entry to every surface,
/// not only every cell. They match the desktop's own menu wording.
pub fn surface_candidates() -> Vec<SpotterEntry> {
    let mut out = vec![
        SpotterEntry {
            label: "World Explorer  (ledger · chronicle · Σ)".to_string(),
            sublabel: "surface · the map of everything".to_string(),
            target: SpotterTarget::WorldExplorer,
            score: 0,
        },
        SpotterEntry {
            label: "World Transcript  (receipt log)".to_string(),
            sublabel: "surface · every committed turn".to_string(),
            target: SpotterTarget::WorldTranscript,
            score: 0,
        },
        SpotterEntry {
            label: "Agent Room  (receipts · mandate · reach)".to_string(),
            sublabel: "surface · the resident, as the executor accounts for it".to_string(),
            target: SpotterTarget::AgentRoom,
            score: 0,
        },
        SpotterEntry {
            label: "Co-author a Document  (branch · stitch · resolve)".to_string(),
            sublabel: "surface · a confined co-author draft, ready to diverge + merge".to_string(),
            target: SpotterTarget::DocCollab,
            score: 0,
        },
    ];
    // The World-Status board (the agent-composable ViewNode surface) sits beside the
    // native chrome only when the content-IR pane is compiled in.
    #[cfg(feature = "card-pane")]
    out.push(SpotterEntry {
        label: "World-Status Board  (deos.ui ViewNode · agent-composable)".to_string(),
        sublabel: "surface · live state the agent reflects-on + rewrites".to_string(),
        target: SpotterTarget::PortableCard,
        score: 0,
    });
    // The discord-bot surface — the desktop face of the one dregg-driven bot (drive its
    // ops as dregg turns + the activity feed as a card) — only when the card pane is in.
    #[cfg(feature = "card-pane")]
    out.push(SpotterEntry {
        label: "discord-bot  (drive its ops · activity feed · ViewNode card)".to_string(),
        sublabel: "surface · the desktop + Discord as two faces of one dregg-driven bot"
            .to_string(),
        target: SpotterTarget::BotSurface,
        score: 0,
    });
    // The confined Android cell + its SystemUI cap-chrome only when that half is built in.
    #[cfg(feature = "android-systemui")]
    out.push(SpotterEntry {
        label: "Android Cell  (SystemUI cap-chrome · hand-over)".to_string(),
        sublabel: "surface · a confined app's caps on the glass; a tap grants a real cap"
            .to_string(),
        target: SpotterTarget::AndroidCell,
        score: 0,
    });
    out
}

// ── The result-row presentation (pure elements, no interactivity) ─────────────────

/// Render the spotter result rows as inert elements — one row per entry, the label in
/// bold over a dim sublabel, the row at `selected` highlighted (navy fill, white text).
/// No click/hover wiring: the desktop View wraps each returned `AnyElement` in its own
/// `cx.listener` for selection + dispatch and threads the arrow-key cursor through
/// `selected`. The geometry matches the context-menu rows (the same dense NT feel).
pub fn render_spotter_rows(entries: &[SpotterEntry], selected: usize) -> Vec<AnyElement> {
    entries
        .iter()
        .enumerate()
        .map(|(i, e)| {
            let is_sel = i == selected;
            bevel_raised(div())
                .px_3()
                .py_1()
                .flex()
                .flex_col()
                .when(is_sel, |d| d.bg(gpui::rgb(NT_SELECT)))
                .child(
                    div()
                        .text_size(px(12.0))
                        .font_weight(FontWeight::BOLD)
                        .text_color(gpui::rgb(if is_sel { NT_TITLE_TEXT } else { NT_TEXT }))
                        .child(e.label.clone()),
                )
                .child(
                    div()
                        .text_size(px(10.0))
                        .text_color(gpui::rgb(if is_sel { NT_FACE_DARK } else { NT_DIM }))
                        .child(e.sublabel.clone()),
                )
                .into_any_element()
        })
        .collect()
}

// ── Unit tests for the pure ranking core (gpui-free) ──────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn entry(label: &str) -> SpotterEntry {
        SpotterEntry {
            label: label.to_string(),
            sublabel: String::new(),
            target: SpotterTarget::Cell(CellId::from_bytes([0u8; 32])),
            score: 0,
        }
    }

    fn labels(v: &[SpotterEntry]) -> Vec<&str> {
        v.iter().map(|e| e.label.as_str()).collect()
    }

    #[test]
    fn exact_subsequence_ranks_above_scattered() {
        // "open" is a contiguous run in the first label, but scattered in the second.
        let cands = vec![entry("Open Document"), entry("Outer pension network")];
        let ranked = rank("open", &cands);
        assert_eq!(ranked.len(), 2, "both labels subsequence-match 'open'");
        assert_eq!(
            ranked[0].label, "Open Document",
            "the contiguous match outranks the scattered one"
        );
    }

    #[test]
    fn word_start_beats_mid_word() {
        // "doc" lands at a word start in the first label, and mid-word in the second
        // ("en-DOC-rine" — the d/o/c run starts inside the word, not at its head). The
        // labels are kept comparable in length so the word-start bonus is decisive.
        let cands = vec![entry("alpha doc here"), entry("endocrine xy")];
        let ranked = rank("doc", &cands);
        assert_eq!(ranked.len(), 2, "both labels subsequence-match 'doc'");
        assert_eq!(
            ranked[0].label, "alpha doc here",
            "a word-start match outranks a mid-word match"
        );
    }

    #[test]
    fn empty_query_returns_all_in_order() {
        let cands = vec![entry("zeta"), entry("alpha"), entry("mu")];
        let ranked = rank("", &cands);
        assert_eq!(
            labels(&ranked),
            vec!["zeta", "alpha", "mu"],
            "an empty query returns every candidate in input order"
        );
        // Whitespace-only queries are treated as empty too.
        let ranked_ws = rank("   ", &cands);
        assert_eq!(labels(&ranked_ws), vec!["zeta", "alpha", "mu"]);
    }

    #[test]
    fn non_matching_query_drops_the_entry() {
        let cands = vec![entry("Inspect account"), entry("Transcript log")];
        let ranked = rank("zzz", &cands);
        assert!(ranked.is_empty(), "no label subsequence-matches 'zzz'");

        // A partial non-match drops only the offending entry.
        let mixed = vec![entry("Inspect account"), entry("Workflow")];
        let ranked2 = rank("insp", &mixed);
        assert_eq!(labels(&ranked2), vec!["Inspect account"]);
    }

    #[test]
    fn match_is_case_insensitive() {
        let cands = vec![entry("Inspect Account 1A2B")];
        // Upper, lower, and mixed query casings all match the same label.
        for q in ["INSPECT", "inspect", "InSpEcT", "1a2b", "1A2B"] {
            let ranked = rank(q, &cands);
            assert_eq!(ranked.len(), 1, "case-insensitive: {q:?} should match");
        }
    }

    #[test]
    fn shorter_label_wins_for_equal_match() {
        // Both contain "ins" at the head; the tighter label should rank first.
        let cands = vec![
            entry("Inspect this long sprawling cell label here"),
            entry("Inspect"),
        ];
        let ranked = rank("ins", &cands);
        assert_eq!(ranked[0].label, "Inspect", "the shorter label wins the tie");
    }
}
