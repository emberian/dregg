//! **The SPOTTER** — a Pharo-style fuzzy command palette for the deos desktop.
//!
//! Pharo's Spotter is the single keystroke that ties every surface together: you
//! summon a floating overlay, type anything, and jump — to a CELL (by id-prefix or
//! kind), to an ACTION on that cell (open as document, explore, inspect, links,
//! transcript, workflow), or to an open WINDOW. It produces a ranked list of
//! candidate entries; selecting one dispatches the corresponding desktop gesture.
//!
//! ## The COMMAND LINE
//!
//! The Spotter is also the desktop's REPL over the formally-verified World: a query
//! whose head parses as a VERB (`transfer 500 to 87a5` · `grant ccfc9955` ·
//! `bump 2a69` · `seal 2a69` — see [`parse_command`]) synthesizes ready-to-commit
//! COMMAND entries above every fuzzy match. Dispatching one fires the SAME
//! verified-turn actuation the right-click context menu fires — receipted, verdict
//! narrated (`committed` / `REFUSED — reason`, with the chronicle height) — so
//! typing a sentence and pressing Enter IS a real turn on the live ledger. Commands
//! rank above fuzzy matches ONLY when the verb prefix parses; any other query is the
//! untouched fuzzy jump.
//!
//! ## The clobber-safe split
//!
//! This module owns the DATA MODEL ([`SpotterTarget`], [`SpotterEntry`]), the pure
//! [`rank`] scorer (the load-bearing, unit-testable core), the pure command GRAMMAR
//! ([`SpotterCommand`], [`parse_command`], [`replay_string`]), the
//! [`candidates_for_cells`] / [`window_candidates`] builders, and a pure
//! [`render_spotter_rows`] presentation fn that returns inert result rows (each
//! wearing its [`entry_badge`] kind chip). The desktop View (`DeosDesktop`) owns the
//! text input, the open-windows map, the cell-prefix RESOLUTION against the live
//! ledger, the recent-jumps trail, the `cx.listener` click/arrow wiring, and the
//! actual dispatch of a selected [`SpotterTarget`]. The fuzzy match, scoring, and
//! grammar are gpui-free, so they compile and test without a renderer.

use gpui::prelude::FluentBuilder;
use gpui::{div, px, AnyElement, FontWeight, IntoElement, ParentElement, Styled};

use dregg_types::CellId;

use crate::deos_desktop::chrome::{
    bevel_raised, id_short, kind_glow, kind_short, NT_DIM, NT_FACE_DARK, NT_LABEL, NT_OK,
    NT_SELECT, NT_TEXT, NT_TITLE_TEXT,
};
use crate::deos_desktop::layout::WinKindTag;

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
    /// Open the PROVENANCE WALKER — the receipt chain walked hash-by-hash, every
    /// link (state-root handoff + blocklace back-edge) RECOMPUTED as you walk. A
    /// global surface: anchored on the walker's own sentinel cell by the dispatcher.
    ProvenanceWalker,
    /// Open the MAIL ROOM — mail between agents as cells on the live World (inbox ·
    /// outbox · mail-ledger; a *deliver now* button fires one ferry round). A global
    /// surface: anchored on the room's own sentinel cell by the dispatcher.
    MailRoom,
    /// Open MY DREGG COMPUTERS — the vats (private verified Worlds on a DreggNet
    /// ServerFleet, each a content-addressed cell) this account can reach: the
    /// roster off the designed `GET /v1/vats` seam, CONNECT attaching one over
    /// the proven HTTP+SSE wire path, its remote cells + receipt stream
    /// reflected live. A global surface: anchored on its own sentinel cell by
    /// the dispatcher.
    DreggComputers,
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
    /// Open the MATRIX ROOM — membrane-over-Matrix in the shipped desktop: rooms as
    /// live cells, sends as receipted turns read back off the receipt chain, the
    /// REAL executor envelope legs over the recorded sync (the live homeserver a
    /// named env-gated seam). A global surface, anchored on the room's own sentinel
    /// cell by the dispatcher. Gated on `dev-surfaces` (the `deos-matrix` wire).
    #[cfg(feature = "dev-surfaces")]
    MatrixRoom,
    /// Open the ATTACH WIZARD — the warm "send your AI to live here" onboarding over
    /// the hireling rail (name · brain · mandate · hire → a real confined resident in
    /// the Agent Room, already stepping). A global surface, anchored on the wizard's
    /// own sentinel cell by the dispatcher. Gated on `dev-surfaces` (the hireling rail).
    #[cfg(feature = "dev-surfaces")]
    AttachWizard,
    /// Jump to an ALREADY-OPEN window — raise it, un-minimize it, and land mold-ready
    /// (the halo-selected arrival every other jump makes). The module doc has promised
    /// "or to an open WINDOW" since the Spotter was born; these entries (built by
    /// [`window_candidates`], front-most first) deliver it. Carries the window's
    /// `(cell, kind)` key — the desktop's `WinKey`.
    FocusWindow(CellId, WinKindTag),
    /// **COMMAND: transfer `amount` from `src` to `dst`** — a real verified transfer
    /// turn between two RESOLVED cells (the View resolved the typed id-prefixes
    /// against the live ledger before synthesizing this entry). Dispatch routes
    /// through the same one-transfer-turn body the compose-drop gesture commits.
    CmdTransfer {
        src: CellId,
        dst: CellId,
        amount: u64,
    },
    /// **COMMAND: grant `src` a capability reaching `dst`** — the context menu's
    /// `Grant` verb (`ActionKind::Grant`) fired from the keyboard; a real
    /// `GrantCapability` turn at the next free slot.
    CmdGrant { src: CellId, dst: CellId },
    /// **COMMAND: bump the cell's nonce** — the context menu's `Bump nonce` verb
    /// (`ActionKind::BumpNonce`); the simplest always-available receipted turn.
    CmdBump(CellId),
    /// **COMMAND: seal / unseal the cell** — the context menu's lifecycle verb
    /// (`ActionKind::ToggleSeal`); seals a live cell, unseals a sealed one.
    CmdSeal(CellId),
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

// ── The command grammar — the pure, unit-testable verb parser ─────────────────────

/// A parsed Spotter COMMAND — the verb vocabulary of the palette-as-command-line.
/// Cell arguments are carried as the typed id-PREFIXES (lowercased hex, unresolved):
/// the pure parser knows no ledger; the desktop View resolves each prefix against
/// the live cells (`id_hex` starts-with) and synthesizes one ready entry per
/// resolution, dispatching the SAME verified-turn actuations the context menu fires.
/// A `None` source means "the operator's own cell" (the desktop's user anchor).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SpotterCommand {
    /// `transfer <amount> [from <src>] [to] <dst>` — a real transfer turn.
    Transfer {
        amount: u64,
        src: Option<String>,
        dst: String,
    },
    /// `grant [<src>] [to] <dst>` — a real `GrantCapability` turn (reach `dst`).
    Grant { src: Option<String>, dst: String },
    /// `bump <cell>` — a real `IncrementNonce` turn.
    Bump { target: String },
    /// `seal <cell>` — a real seal/unseal lifecycle turn (toggles on dispatch).
    Seal { target: String },
}

/// Parse `query` as a Spotter COMMAND, or `None` when it is not one (the query then
/// stays a plain fuzzy jump — commands never shadow the fuzzy match unless the verb
/// prefix actually parses, which is the palette's no-regression contract).
///
/// The grammar (case-insensitive; the `from` / `to` connectives are optional prose
/// and can never collide with a cell prefix — their letters are not hex digits):
///
/// ```text
/// transfer <amount> [from <src>] [to] <dst>      "transfer 500 to 87a5"
/// grant [<src>] [to] <dst>                       "grant ccfc9955"
/// bump <cell>                                    "bump 2a69"
/// seal <cell>                                    "seal 2a69"   (toggles seal/unseal)
/// ```
///
/// A cell argument is a hex id-prefix (2–64 hex chars); amounts take `,` / `_`
/// separators (`1,000`). Anything missing, malformed, or extra parses to `None`,
/// so a half-typed command degrades to fuzzy ranking keystroke by keystroke and
/// only a whole, well-formed sentence puts a command on top.
pub fn parse_command(query: &str) -> Option<SpotterCommand> {
    let toks: Vec<String> = query.split_whitespace().map(str::to_lowercase).collect();
    let (verb, args) = toks.split_first()?;
    // Drop the prose connectives; what remains must be exactly the verb's arguments.
    let args: Vec<&str> = args
        .iter()
        .map(String::as_str)
        .filter(|t| *t != "from" && *t != "to")
        .collect();
    match verb.as_str() {
        "transfer" => {
            let (amount_tok, prefixes) = args.split_first()?;
            let amount = parse_amount(amount_tok)?;
            match prefixes {
                [dst] => Some(SpotterCommand::Transfer {
                    amount,
                    src: None,
                    dst: valid_prefix(dst)?,
                }),
                [src, dst] => Some(SpotterCommand::Transfer {
                    amount,
                    src: Some(valid_prefix(src)?),
                    dst: valid_prefix(dst)?,
                }),
                _ => None,
            }
        }
        "grant" => match args.as_slice() {
            [dst] => Some(SpotterCommand::Grant {
                src: None,
                dst: valid_prefix(dst)?,
            }),
            [src, dst] => Some(SpotterCommand::Grant {
                src: Some(valid_prefix(src)?),
                dst: valid_prefix(dst)?,
            }),
            _ => None,
        },
        "bump" => match args.as_slice() {
            [c] => Some(SpotterCommand::Bump {
                target: valid_prefix(c)?,
            }),
            _ => None,
        },
        "seal" => match args.as_slice() {
            [c] => Some(SpotterCommand::Seal {
                target: valid_prefix(c)?,
            }),
            _ => None,
        },
        _ => None,
    }
}

/// Validate a (lowercased) cell id-prefix argument: 2–64 hex chars. One char would
/// fan out to a sixteenth of the ledger; more than 64 can prefix no id at all.
fn valid_prefix(t: &str) -> Option<String> {
    ((2..=64).contains(&t.len()) && t.chars().all(|c| c.is_ascii_hexdigit())).then(|| t.to_string())
}

/// Parse an amount token, tolerating `,` / `_` grouping (`1,000` · `25_000`).
fn parse_amount(t: &str) -> Option<u64> {
    let digits: String = t.chars().filter(|c| *c != ',' && *c != '_').collect();
    if digits.is_empty() || !digits.chars().all(|c| c.is_ascii_digit()) {
        return None;
    }
    digits.parse().ok()
}

/// The string that RE-RUNS a dispatched entry from the recent-jumps trail. For a
/// command it is the canonical verb line over the RESOLVED cells' short ids (which
/// [`parse_command`] re-parses, so a recalled command re-resolves against the LIVE
/// ledger rather than replaying a stale target); for every other entry it is the
/// label, which the trail matches back to the current candidate set (so a closed
/// window or vanished cell quietly drops out instead of dispatching into nothing).
pub fn replay_string(entry: &SpotterEntry) -> String {
    match &entry.target {
        SpotterTarget::CmdTransfer { src, dst, amount } => {
            format!("transfer {} {} {}", amount, id_short(src), id_short(dst))
        }
        SpotterTarget::CmdGrant { src, dst } => {
            format!("grant {} {}", id_short(src), id_short(dst))
        }
        SpotterTarget::CmdBump(c) => format!("bump {}", id_short(c)),
        SpotterTarget::CmdSeal(c) => format!("seal {}", id_short(c)),
        _ => entry.label.clone(),
    }
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
            label: "Provenance Walker  (receipt chain · hash-by-hash)".to_string(),
            sublabel: "surface · every link recomputed as you walk, never trusted".to_string(),
            target: SpotterTarget::ProvenanceWalker,
            score: 0,
        },
        SpotterEntry {
            label: "Mail Room  (letters as cells · inbox · outbox · deliver)".to_string(),
            sublabel: "surface · mail between agents; a letter IS a cell, delivery a turn"
                .to_string(),
            target: SpotterTarget::MailRoom,
            score: 0,
        },
        SpotterEntry {
            label: "My Dregg Computers  (vats you can reach · connect)".to_string(),
            sublabel: "surface · your private verified Worlds — reflect · receipts · cannot lie"
                .to_string(),
            target: SpotterTarget::DreggComputers,
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
    // The Matrix Room — membranes over the wire — only when the deos-matrix wire
    // types are compiled in (`dev-surfaces`).
    #[cfg(feature = "dev-surfaces")]
    out.push(SpotterEntry {
        label: "Matrix Room  (membranes over the wire · receipted sends)".to_string(),
        sublabel: "surface · rooms as live cells; envelopes rehydrate + drive on the real \
                   executor"
            .to_string(),
        target: SpotterTarget::MatrixRoom,
        score: 0,
    });
    // THE ATTACH WIZARD — the warm front door onto the hireling rail (name · brain ·
    // mandate · hire), only when that rail is compiled in (`dev-surfaces`).
    #[cfg(feature = "dev-surfaces")]
    out.push(SpotterEntry {
        label: "Attach a resident  (send your AI to live here)".to_string(),
        sublabel: "surface · name · brain · mandate · hire → a real resident in the Agent Room"
            .to_string(),
        target: SpotterTarget::AttachWizard,
        score: 0,
    });
    out
}

/// Build the OPEN-WINDOW candidates — one jump-to-window entry per `(title, cell,
/// kind)` row, in the caller's order (the desktop passes front-most first, so the
/// window you touched last is also the first row a bare query greets). These are
/// prepended AHEAD of every other candidate: [`rank`]'s stable sort keeps input
/// order on ties, so "open windows rank first" holds exactly at equal match quality
/// — a strictly stronger fuzzy match elsewhere still wins, and the existing jump
/// vocabulary is not regressed. Dispatching one focuses (raises + un-minimizes) the
/// window and lands mold-ready.
pub fn window_candidates(wins: &[(String, CellId, WinKindTag)]) -> Vec<SpotterEntry> {
    wins.iter()
        .map(|(title, cell, tag)| SpotterEntry {
            label: format!("Window  {title}"),
            sublabel: "open window · jump + focus (raises · un-minimizes)".to_string(),
            target: SpotterTarget::FocusWindow(*cell, *tag),
            score: 0,
        })
        .collect()
}

// ── The row badge — what a row IS, in one fixed-width chip ────────────────────────

/// The `(tag, color)` kind-chip a result row wears, derived purely from the entry:
/// navy `CMD` for a command (it COMMITS), green window-kind tags for open windows
/// (they are already alive on the glass), the cell's kind-glow hue for a bare cell
/// jump, dim gray window-kind tags for per-cell action verbs, and dim tags for the
/// global surfaces. One glance sorts the list; the tags are [`kind_short`]'s — the
/// same vocabulary the taskbar stubs wear.
pub fn entry_badge(entry: &SpotterEntry) -> (&'static str, u32) {
    use SpotterTarget as T;
    match &entry.target {
        T::CmdTransfer { .. } | T::CmdGrant { .. } | T::CmdBump(_) | T::CmdSeal(_) => {
            ("CMD", NT_SELECT)
        }
        T::FocusWindow(_, tag) => (kind_short(*tag), NT_OK),
        // A bare cell jump: the label is "{kind} {short}", so the kind (possibly
        // two words — "issuer well") is everything before the trailing id.
        T::Cell(_) => (
            "CEL",
            kind_glow(entry.label.rsplit_once(' ').map(|(k, _)| k).unwrap_or("")),
        ),
        T::Inspect(_) => (kind_short(WinKindTag::Inspector), NT_LABEL),
        T::OpenDoc(_) => (kind_short(WinKindTag::DocEditor), NT_LABEL),
        T::Explore(_) => (kind_short(WinKindTag::DocExplorer), NT_LABEL),
        T::Links(_) => (kind_short(WinKindTag::Links), NT_LABEL),
        T::Transcript(_) => (kind_short(WinKindTag::Transcript), NT_LABEL),
        T::Workflow(_) => (kind_short(WinKindTag::Workflow), NT_LABEL),
        T::WorldExplorer => (kind_short(WinKindTag::WorldExplorer), NT_LABEL),
        T::AgentRoom => (kind_short(WinKindTag::AgentRoom), NT_LABEL),
        T::ProvenanceWalker => (kind_short(WinKindTag::ProvenanceWalker), NT_LABEL),
        T::MailRoom => (kind_short(WinKindTag::MailRoom), NT_LABEL),
        T::DreggComputers => (kind_short(WinKindTag::DreggComputers), NT_LABEL),
        T::WorldTranscript => (kind_short(WinKindTag::Transcript), NT_LABEL),
        T::DocCollab => (kind_short(WinKindTag::DocEditor), NT_LABEL),
        #[cfg(feature = "card-pane")]
        T::PortableCard => (kind_short(WinKindTag::ViewNodePane), NT_LABEL),
        #[cfg(feature = "card-pane")]
        T::BotSurface => ("BOT", NT_LABEL),
        #[cfg(feature = "android-systemui")]
        T::AndroidCell => (kind_short(WinKindTag::AndroidCell), NT_LABEL),
        #[cfg(feature = "app-registry")]
        T::AppShelf | T::LaunchApp(_) => (kind_short(WinKindTag::AppShelf), NT_LABEL),
        #[cfg(feature = "app-registry")]
        T::ExchangeFloor => (kind_short(WinKindTag::ExchangeFloor), NT_LABEL),
        #[cfg(feature = "dev-surfaces")]
        T::MatrixRoom => (kind_short(WinKindTag::MatrixRoom), NT_LABEL),
        #[cfg(feature = "dev-surfaces")]
        T::AttachWizard => (kind_short(WinKindTag::AttachWizard), NT_LABEL),
    }
}

// ── The result-row presentation (pure elements, no interactivity) ─────────────────

/// Render the spotter result rows as inert elements — one row per entry: the
/// [`entry_badge`] kind chip, then the label in bold over a dim sublabel; the row at
/// `selected` highlighted (navy fill, white text — the chip goes white too, so the
/// selected row is one coherent NT inversion). No click/hover wiring: the desktop
/// View wraps each returned `AnyElement` in its own `cx.listener` for selection +
/// dispatch and threads the arrow-key cursor through `selected`. The geometry
/// matches the context-menu rows (the same dense NT feel).
pub fn render_spotter_rows(entries: &[SpotterEntry], selected: usize) -> Vec<AnyElement> {
    entries
        .iter()
        .enumerate()
        .map(|(i, e)| {
            let is_sel = i == selected;
            let (tag, color) = entry_badge(e);
            bevel_raised(div())
                .px_3()
                .py_1()
                .flex()
                .flex_row()
                .items_center()
                .gap_2()
                .when(is_sel, |d| d.bg(gpui::rgb(NT_SELECT)))
                .child(
                    // The kind chip — fixed-width so the label column stays ruled.
                    div()
                        .w(px(30.0))
                        .flex_none()
                        .text_size(px(9.0))
                        .font_weight(FontWeight::BOLD)
                        .text_color(gpui::rgb(if is_sel { NT_TITLE_TEXT } else { color }))
                        .child(tag),
                )
                .child(
                    div()
                        .flex_1()
                        .flex()
                        .flex_col()
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
                        ),
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

    // ── The command grammar ──────────────────────────────────────────────────────

    #[test]
    fn parse_command_reads_the_daily_driver_verbs() {
        // The scout plan's three headline sentences, verbatim.
        assert_eq!(
            parse_command("transfer 500 to 87a5"),
            Some(SpotterCommand::Transfer {
                amount: 500,
                src: None,
                dst: "87a5".into(),
            })
        );
        assert_eq!(
            parse_command("grant ccfc9955"),
            Some(SpotterCommand::Grant {
                src: None,
                dst: "ccfc9955".into(),
            })
        );
        assert_eq!(
            parse_command("bump 2a69"),
            Some(SpotterCommand::Bump {
                target: "2a69".into(),
            })
        );
        assert_eq!(
            parse_command("seal 2a69"),
            Some(SpotterCommand::Seal {
                target: "2a69".into(),
            })
        );
    }

    #[test]
    fn parse_command_takes_full_and_connective_forms() {
        // Two-prefix transfer, bare and dressed in `from … to …` prose — one shape.
        let full = Some(SpotterCommand::Transfer {
            amount: 1_000,
            src: Some("1a2b".into()),
            dst: "9f3c".into(),
        });
        assert_eq!(parse_command("transfer 1,000 1a2b 9f3c"), full);
        assert_eq!(parse_command("transfer 1000 from 1a2b to 9f3c"), full);
        assert_eq!(parse_command("transfer 1_000 1a2b to 9f3c"), full);
        // Grant with an explicit source.
        assert_eq!(
            parse_command("grant 1a2b to ccfc"),
            Some(SpotterCommand::Grant {
                src: Some("1a2b".into()),
                dst: "ccfc".into(),
            })
        );
    }

    #[test]
    fn parse_command_is_case_insensitive_and_lowercases_prefixes() {
        assert_eq!(
            parse_command("Transfer 500 TO 87A5"),
            Some(SpotterCommand::Transfer {
                amount: 500,
                src: None,
                dst: "87a5".into(),
            }),
            "verbs, connectives, and hex prefixes all read case-insensitively"
        );
    }

    #[test]
    fn parse_command_rejects_non_commands_and_half_typed_ones() {
        // Not verbs — ordinary fuzzy queries must NEVER parse (the no-regression
        // contract: commands rank above fuzzy only when the verb prefix parses).
        for q in [
            "",
            "world explorer",
            "inspect 87a5",
            "doc",
            "agent room",
            "co-author document",
        ] {
            assert_eq!(parse_command(q), None, "{q:?} is not a command");
        }
        // Half-typed / malformed commands degrade to fuzzy, keystroke by keystroke.
        for q in [
            "transfer",
            "transfer 500",               // no destination yet
            "transfer x to 87a5",         // amount is not a number
            "transfer 500 to zz99",       // 'z' is not a hex digit
            "transfer 500 to 87a5 extra", // trailing junk
            "grant",
            "bump",
            "bump a",         // a 1-char prefix fans out to a sixteenth of the ledger
            "bump 2a69 2b70", // one cell only
            "seal",
        ] {
            assert_eq!(parse_command(q), None, "{q:?} must not parse");
        }
    }

    #[test]
    fn replay_string_roundtrips_a_command_through_the_parser() {
        // A dispatched command's replay line re-parses to the same command shape
        // over the resolved cells' short ids — the recent-jumps trail re-resolves
        // against the LIVE ledger instead of replaying a stale target.
        let (src, dst) = (CellId::from_bytes([1u8; 32]), CellId::from_bytes([2u8; 32]));
        let e = SpotterEntry {
            label: "Transfer 500  account 01010101 → account 02020202".into(),
            sublabel: String::new(),
            target: SpotterTarget::CmdTransfer {
                src,
                dst,
                amount: 500,
            },
            score: 0,
        };
        assert_eq!(
            parse_command(&replay_string(&e)),
            Some(SpotterCommand::Transfer {
                amount: 500,
                src: Some(id_short(&src)),
                dst: id_short(&dst),
            })
        );
        // A plain jump replays as its label (matched back to the live candidates).
        assert_eq!(
            replay_string(&entry("Inspect  account 1a2b")),
            "Inspect  account 1a2b"
        );
    }

    // ── The open-window candidates + the row badges ─────────────────────────────

    #[test]
    fn window_candidates_carry_focus_targets_in_input_order() {
        let a = CellId::from_bytes([3u8; 32]);
        let b = CellId::from_bytes([4u8; 32]);
        let wins = vec![
            (
                "account 0303 — Document".to_string(),
                a,
                WinKindTag::DocEditor,
            ),
            (
                "treasury 0404 — Inspector".to_string(),
                b,
                WinKindTag::Inspector,
            ),
        ];
        let cands = window_candidates(&wins);
        assert_eq!(
            labels(&cands),
            vec![
                "Window  account 0303 — Document",
                "Window  treasury 0404 — Inspector",
            ]
        );
        assert!(
            matches!(cands[0].target, SpotterTarget::FocusWindow(c, WinKindTag::DocEditor) if c == a),
            "the entry targets the window's (cell, kind) key"
        );
    }

    #[test]
    fn entry_badge_sorts_the_list_at_a_glance() {
        // A command wears the navy CMD chip.
        let cmd = SpotterEntry {
            label: "Bump nonce  account 2a69".into(),
            sublabel: String::new(),
            target: SpotterTarget::CmdBump(CellId::from_bytes([5u8; 32])),
            score: 0,
        };
        assert_eq!(entry_badge(&cmd), ("CMD", NT_SELECT));
        // An open window wears its kind tag in the live green.
        let win = SpotterEntry {
            label: "Window  account 0303 — Document".into(),
            sublabel: String::new(),
            target: SpotterTarget::FocusWindow(
                CellId::from_bytes([3u8; 32]),
                WinKindTag::DocEditor,
            ),
            score: 0,
        };
        assert_eq!(entry_badge(&win), ("DOC", NT_OK));
        // A bare cell jump glows its kind's hue — including a two-word kind.
        let cell = SpotterEntry {
            label: "issuer well 1a2b3c4d".into(),
            sublabel: String::new(),
            target: SpotterTarget::Cell(CellId::from_bytes([6u8; 32])),
            score: 0,
        };
        assert_eq!(entry_badge(&cell), ("CEL", kind_glow("issuer well")));
    }
}
