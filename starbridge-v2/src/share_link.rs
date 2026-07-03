//! THE DESKTOP IN A LINK — the share-URL tape codec (pure, gpui-free).
//!
//! A shared deos desktop is NOT a screenshot and NOT a serialized blob of
//! state. It is a **tape**: a pinned genesis instant plus the sequence of
//! messages a session sent, small enough to live in a URL fragment. The
//! recipient's viewer boots a FRESH world at the pinned instant
//! ([`crate::world::demo_world_at`]) and RE-EXECUTES the tape through the same
//! embedded verified executor — reconstructing the sharer's desktop by
//! re-derivation, never by trust. The optional `root` claim closes the loop:
//! the sharer bakes their canonical ledger root into the link, the viewer
//! re-derives its own after replay, and the page headline is the EQUALITY
//! (or, honestly, the divergence). "You did not trust my screenshot — you
//! re-derived my desktop."
//!
//! ## The fragment grammar (`deos1`)
//!
//! ```text
//! deos1!ts=<i64>[!tab=<esc>][!root=<64 lowercase hex>][!act=<cellhex>:<esc>]*
//! ```
//!
//! * `ts`   — REQUIRED, exactly once: the pinned wall-clock
//!            ([`crate::world::World::with_costs_and_timestamp`] folds it into
//!            every receipt hash, so byte-identical replay REQUIRES sharing it).
//! * `tab`  — optional: the cockpit surface the sharer was looking at
//!            (`select_tab_named` vocabulary), so the frame reconstructs the
//!            same view, not just the same world.
//! * `root` — optional: the sharer's claimed canonical ledger root
//!            (`persistence::canonical_ledger_root`), 64 lowercase hex chars.
//! * `act`  — repeatable, in order: one message of the tape —
//!            `<cell hex-id prefix>:<affordance verb>`, the SAME
//!            `(cell, message)` vocabulary the `--replay` bake flag and the
//!            dregg-mcp act log already speak.
//!
//! Every character the encoder emits is fragment- AND query-safe per RFC 3986
//! (`!` `=` `:` `.` `~` `-` `_` and alphanumerics), so the SAME string rides
//! `https://…/deos-viewer/#<fragment>` and the serve-ie6 server's
//! `GET /shared?d=<fragment>` untouched — no percent-encoding layer to drift.
//!
//! ## Fail-closed by construction
//!
//! Decoding REFUSES (never guesses): unknown version tags, duplicate fields,
//! malformed escapes, non-hex cells/roots, over-cap tapes. The caps exist
//! because a share link is STRANGER INPUT to a replaying server: [`MAX_ACTS`]
//! bounds the CPU a link can demand, [`MAX_FRAGMENT_LEN`] keeps the whole
//! request line inside the serve-ie6 server's single 2 KiB read. The viewer is
//! READ-ONLY: a tape replays onto a fresh world; it never reaches the live one.
//!
//! The codec half of this module is PURE std+hex (no gpui, no executor) so it
//! compiles everywhere the crate does — the wasm cockpit can adopt the same
//! format without a port. The replay half ([`replay_onto`]) is gated on
//! `embedded-executor` and drives the REAL [`crate::inspect_act::InspectAct`]
//! send path — the same cap-gate + verified turn every other surface fires.

use std::fmt;

/// The version tag every fragment opens with. Bump ONLY with a new decoder arm
/// (an unknown tag is a refusal, not a guess — links are forever).
pub const VERSION_TAG: &str = "deos1";

/// Decode refuses fragments longer than this. The serve-ie6 server reads the
/// whole request into one 2 KiB buffer; the fragment must leave headroom for
/// `GET /shared?d=` + ` HTTP/1.0` so the request LINE always survives intact.
pub const MAX_FRAGMENT_LEN: usize = 1024;

/// Decode refuses tapes with more acts than this. Each act is a full verified
/// turn on the replaying server — a stranger's link buys a bounded amount of
/// executor time, never an unbounded loop.
pub const MAX_ACTS: usize = 32;

/// Cap on one message verb's RAW byte length (pre-escape). The affordance
/// vocabulary is short words (`peek`/`touch`/`write`/…); 96 bytes is generous.
pub const MAX_MSG_LEN: usize = 96;

/// Cap on the tab name's RAW byte length (`select_tab_named` names are short).
pub const MAX_TAB_LEN: usize = 48;

/// One act of the tape: a message sent to a cell — the SAME `(cell, message)`
/// pair the `--replay <cell>:<msg>` bake flag speaks. `cell` is a lowercase
/// hex PREFIX of the cell id (resolved against the replayed ledger, exactly as
/// the bake resolves it); `msg` is the affordance verb.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShareAct {
    /// Lowercase hex prefix of the target cell id (1..=64 chars).
    pub cell: String,
    /// The message selector — the deos affordance verb to send.
    pub msg: String,
}

/// The whole shareable tape: everything a fresh world needs to re-derive the
/// sharer's desktop, plus the optional root claim that makes the re-derivation
/// CHECKABLE rather than merely repeatable.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShareTape {
    /// The pinned genesis instant (unix seconds). Receipt hashes bind it, so
    /// replay is byte-identical ONLY under the same value — it rides the link.
    pub timestamp: i64,
    /// The cockpit surface the sharer was on (`select_tab_named` vocabulary),
    /// if they chose to share the view along with the world.
    pub tab: Option<String>,
    /// The message tape, in send order.
    pub acts: Vec<ShareAct>,
    /// The sharer's claimed canonical ledger root AFTER the tape — the
    /// convergence tooth the viewer re-derives and compares against.
    pub expected_root: Option<[u8; 32]>,
}

/// Everything [`decode_fragment`] can refuse. Refusals are first-class (the
/// viewer page prints them) — a bad link is SHOWN bad, never silently patched.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShareLinkError {
    /// Fragment exceeds [`MAX_FRAGMENT_LEN`].
    TooLong { len: usize },
    /// The fragment does not open with the `deos1` version tag.
    BadVersion,
    /// A field is not `key=value` shaped, or the key is unknown.
    BadField(String),
    /// A once-only field (`ts`/`tab`/`root`) appeared twice.
    DuplicateField(&'static str),
    /// No `ts` field — a tape without its pinned instant cannot replay
    /// byte-identically, so it does not decode at all.
    MissingTimestamp,
    /// `ts` did not parse as an i64.
    BadTimestamp,
    /// `root` was not exactly 64 lowercase hex chars.
    BadRoot,
    /// An act's cell was not a 1..=64-char lowercase hex prefix.
    BadCell(String),
    /// A `~XX` escape was malformed, or the unescaped bytes were not UTF-8.
    BadEscape,
    /// More than [`MAX_ACTS`] acts.
    TooManyActs { got: usize },
    /// A message verb exceeded [`MAX_MSG_LEN`] raw bytes.
    MsgTooLong,
    /// The tab name exceeded [`MAX_TAB_LEN`] raw bytes.
    TabTooLong,
}

impl fmt::Display for ShareLinkError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ShareLinkError::TooLong { len } => write!(
                f,
                "share fragment is {len} chars (max {MAX_FRAGMENT_LEN}) — refused"
            ),
            ShareLinkError::BadVersion => write!(
                f,
                "share fragment does not open with `{VERSION_TAG}` — unknown format, refused"
            ),
            ShareLinkError::BadField(field) => {
                write!(
                    f,
                    "share fragment field `{field}` is not understood — refused"
                )
            }
            ShareLinkError::DuplicateField(key) => {
                write!(
                    f,
                    "share fragment repeats once-only field `{key}` — refused"
                )
            }
            ShareLinkError::MissingTimestamp => write!(
                f,
                "share fragment carries no `ts` — a tape without its pinned instant \
                 cannot replay byte-identically, refused"
            ),
            ShareLinkError::BadTimestamp => {
                write!(f, "share fragment `ts` is not an i64 — refused")
            }
            ShareLinkError::BadRoot => write!(
                f,
                "share fragment `root` is not 64 lowercase hex chars — refused"
            ),
            ShareLinkError::BadCell(cell) => write!(
                f,
                "share fragment act cell `{cell}` is not a lowercase hex id prefix — refused"
            ),
            ShareLinkError::BadEscape => {
                write!(
                    f,
                    "share fragment carries a malformed `~XX` escape — refused"
                )
            }
            ShareLinkError::TooManyActs { got } => write!(
                f,
                "share fragment carries {got} acts (max {MAX_ACTS}) — refused"
            ),
            ShareLinkError::MsgTooLong => write!(
                f,
                "share fragment message verb exceeds {MAX_MSG_LEN} bytes — refused"
            ),
            ShareLinkError::TabTooLong => write!(
                f,
                "share fragment tab name exceeds {MAX_TAB_LEN} bytes — refused"
            ),
        }
    }
}

impl std::error::Error for ShareLinkError {}

// ─── the escape layer ────────────────────────────────────────────────────────
//
// Message verbs and tab names are ARBITRARY strings in principle (the
// affordance vocabulary is data, not a closed enum), so they get a tiny
// self-contained escape: bytes in [A-Za-z0-9._-] pass through, everything else
// (INCLUDING `~` itself) becomes `~XX` (two uppercase hex digits of the UTF-8
// byte). Every emitted char is fragment- and query-safe; decode is fail-closed
// (a dangling or non-hex escape refuses, and the unescaped bytes must be UTF-8).

/// Is `b` a byte the escape layer passes through verbatim?
fn plain(b: u8) -> bool {
    b.is_ascii_alphanumeric() || matches!(b, b'.' | b'_' | b'-')
}

/// Escape `s` for a fragment field value. Total: every string has exactly one
/// escaped form, and every escaped form round-trips ([`unesc`] ∘ `esc` = id).
fn esc(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for &b in s.as_bytes() {
        if plain(b) {
            out.push(b as char);
        } else {
            out.push('~');
            out.push_str(&format!("{b:02X}"));
        }
    }
    out
}

/// Reverse [`esc`]. Fail-closed: malformed escapes and non-UTF-8 results refuse.
fn unesc(s: &str) -> Result<String, ShareLinkError> {
    let bytes = s.as_bytes();
    let mut out: Vec<u8> = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'~' => {
                let hi = bytes.get(i + 1).ok_or(ShareLinkError::BadEscape)?;
                let lo = bytes.get(i + 2).ok_or(ShareLinkError::BadEscape)?;
                let hex2 = [*hi, *lo];
                let hexstr = std::str::from_utf8(&hex2).map_err(|_| ShareLinkError::BadEscape)?;
                let byte = u8::from_str_radix(hexstr, 16).map_err(|_| ShareLinkError::BadEscape)?;
                out.push(byte);
                i += 3;
            }
            b if plain(b) => {
                out.push(b);
                i += 1;
            }
            // Anything else in an escaped value is a smuggled raw char — refuse
            // (the encoder never emits it, so a decoder seeing it has a bad link).
            _ => return Err(ShareLinkError::BadEscape),
        }
    }
    String::from_utf8(out).map_err(|_| ShareLinkError::BadEscape)
}

// ─── encode ──────────────────────────────────────────────────────────────────

/// Encode `tape` as a URL-fragment string (canonical field order:
/// `ts`, `tab?`, `root?`, `act*`). Fail-closed on BOTH ends: an over-cap tape
/// refuses to encode, for the same reasons decode refuses it — a link the
/// decoder would bounce should never be minted.
pub fn encode_fragment(tape: &ShareTape) -> Result<String, ShareLinkError> {
    if tape.acts.len() > MAX_ACTS {
        return Err(ShareLinkError::TooManyActs {
            got: tape.acts.len(),
        });
    }
    let mut out = String::from(VERSION_TAG);
    out.push_str(&format!("!ts={}", tape.timestamp));
    if let Some(tab) = &tape.tab {
        if tab.len() > MAX_TAB_LEN {
            return Err(ShareLinkError::TabTooLong);
        }
        out.push_str(&format!("!tab={}", esc(tab)));
    }
    if let Some(root) = &tape.expected_root {
        out.push_str(&format!("!root={}", hex::encode(root)));
    }
    for act in &tape.acts {
        if !is_hex_prefix(&act.cell) {
            return Err(ShareLinkError::BadCell(act.cell.clone()));
        }
        if act.msg.len() > MAX_MSG_LEN {
            return Err(ShareLinkError::MsgTooLong);
        }
        out.push_str(&format!("!act={}:{}", act.cell, esc(&act.msg)));
    }
    if out.len() > MAX_FRAGMENT_LEN {
        return Err(ShareLinkError::TooLong { len: out.len() });
    }
    Ok(out)
}

/// Convenience: the full share URL — `base` (the viewer page) + `#` + fragment.
pub fn share_url(base: &str, tape: &ShareTape) -> Result<String, ShareLinkError> {
    Ok(format!("{base}#{}", encode_fragment(tape)?))
}

/// Is `s` a plausible cell-id hex prefix (1..=64 lowercase hex chars)?
fn is_hex_prefix(s: &str) -> bool {
    !s.is_empty() && s.len() <= 64 && s.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'))
}

// ─── decode ──────────────────────────────────────────────────────────────────

/// Decode a fragment string back into a [`ShareTape`].
///
/// Tolerant EXACTLY as far as honesty allows: fields may arrive in any order
/// (links get hand-edited), a leading `#` is shed (callers pass `location.hash`
/// verbatim) — but duplicates, unknown keys, malformed values, and over-cap
/// tapes all REFUSE with a first-class [`ShareLinkError`]. No guessing.
pub fn decode_fragment(s: &str) -> Result<ShareTape, ShareLinkError> {
    let s = s.strip_prefix('#').unwrap_or(s);
    if s.len() > MAX_FRAGMENT_LEN {
        return Err(ShareLinkError::TooLong { len: s.len() });
    }
    let mut parts = s.split('!');
    if parts.next() != Some(VERSION_TAG) {
        return Err(ShareLinkError::BadVersion);
    }

    let mut timestamp: Option<i64> = None;
    let mut tab: Option<String> = None;
    let mut expected_root: Option<[u8; 32]> = None;
    let mut acts: Vec<ShareAct> = Vec::new();

    for field in parts {
        let (key, value) = field
            .split_once('=')
            .ok_or_else(|| ShareLinkError::BadField(field.to_string()))?;
        match key {
            "ts" => {
                if timestamp.is_some() {
                    return Err(ShareLinkError::DuplicateField("ts"));
                }
                timestamp = Some(value.parse().map_err(|_| ShareLinkError::BadTimestamp)?);
            }
            "tab" => {
                if tab.is_some() {
                    return Err(ShareLinkError::DuplicateField("tab"));
                }
                let t = unesc(value)?;
                if t.len() > MAX_TAB_LEN {
                    return Err(ShareLinkError::TabTooLong);
                }
                tab = Some(t);
            }
            "root" => {
                if expected_root.is_some() {
                    return Err(ShareLinkError::DuplicateField("root"));
                }
                if value.len() != 64 || !is_hex_prefix(value) {
                    return Err(ShareLinkError::BadRoot);
                }
                let bytes = hex::decode(value).map_err(|_| ShareLinkError::BadRoot)?;
                let mut root = [0u8; 32];
                root.copy_from_slice(&bytes);
                expected_root = Some(root);
            }
            "act" => {
                if acts.len() >= MAX_ACTS {
                    return Err(ShareLinkError::TooManyActs {
                        got: acts.len() + 1,
                    });
                }
                let (cell, msg) = value
                    .split_once(':')
                    .ok_or_else(|| ShareLinkError::BadField(field.to_string()))?;
                if !is_hex_prefix(cell) {
                    return Err(ShareLinkError::BadCell(cell.to_string()));
                }
                let msg = unesc(msg)?;
                if msg.len() > MAX_MSG_LEN {
                    return Err(ShareLinkError::MsgTooLong);
                }
                acts.push(ShareAct {
                    cell: cell.to_string(),
                    msg,
                });
            }
            _ => return Err(ShareLinkError::BadField(field.to_string())),
        }
    }

    Ok(ShareTape {
        timestamp: timestamp.ok_or(ShareLinkError::MissingTimestamp)?,
        tab,
        acts,
        expected_root,
    })
}

// ─── the replay half (embedded-executor only) ────────────────────────────────

/// The convergence verdict after a replay — the headline of the viewer page.
#[cfg(feature = "embedded-executor")]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RootVerdict {
    /// The link claimed a root and the re-derived one EQUALS it — the recipient
    /// re-derived the sharer's desktop, byte-for-byte at the ledger.
    Match([u8; 32]),
    /// The link claimed a root and the re-derived one DIFFERS. Surfaced, never
    /// smoothed over: the code moved, the tape was edited, or an act refused.
    Mismatch {
        claimed: [u8; 32],
        derived: [u8; 32],
    },
    /// The link made no claim; here is the root the replay derived (a sharer
    /// can paste it back into the link as `!root=…` to make it checkable).
    Unclaimed([u8; 32]),
}

/// What one tape replay actually did — committed turns, in-band skips (an act
/// whose cell no longer resolves or whose send refused — surfaced, not
/// swallowed), and the root verdict.
#[cfg(feature = "embedded-executor")]
#[derive(Debug)]
pub struct ReplayOutcome {
    /// How many acts committed as real verified turns.
    pub committed: usize,
    /// `(act index, reason)` for every act that did NOT commit. A non-empty
    /// list means the reconstruction is NOT the sharer's desktop — the page
    /// says so (and the root verdict almost certainly says Mismatch).
    pub skipped: Vec<(usize, String)>,
    /// The convergence verdict (see [`RootVerdict`]).
    pub verdict: RootVerdict,
}

/// Replay `tape` onto `world` — the EXACT `--replay` bake semantics: resolve
/// each act's cell by hex-id prefix against the live ledger, then send the
/// message through the real [`crate::inspect_act::InspectAct`] as the cell
/// upon itself at the `Either` tier (the same self-operator projection the
/// inspect→act panel uses). Refusals are RECORDED in the outcome (the viewer
/// page prints them), never silently dropped. Afterward the canonical ledger
/// root is derived and judged against the tape's claim.
///
/// The caller supplies the world so the base image is explicit —
/// [`replay_fresh`] is the fresh-boot wrapper the share route uses.
#[cfg(feature = "embedded-executor")]
pub fn replay_onto(world: &mut crate::world::World, tape: &ShareTape) -> ReplayOutcome {
    use crate::inspect_act::{InspectAct, InspectFocus, SendResult};
    use dregg_cell::permissions::AuthRequired;

    let mut committed = 0usize;
    let mut skipped: Vec<(usize, String)> = Vec::new();
    for (i, act) in tape.acts.iter().enumerate() {
        let resolved =
            world.ledger().iter().map(|(id, _)| *id).find(|id| {
                hex::encode(id.as_bytes()).starts_with(act.cell.trim_start_matches("0x"))
            });
        let Some(cell) = resolved else {
            skipped.push((i, format!("no cell matches prefix `{}`", act.cell)));
            continue;
        };
        let ia = InspectAct::build(world, InspectFocus::Cell(cell), cell, AuthRequired::Either);
        match ia.send(world, &act.msg, AuthRequired::Either) {
            SendResult::Committed { .. } => committed += 1,
            SendResult::Refused { reason, .. } => skipped.push((i, reason)),
        }
    }

    let derived = crate::persistence::canonical_ledger_root(world.ledger());
    let verdict = match tape.expected_root {
        Some(claimed) if claimed == derived => RootVerdict::Match(derived),
        Some(claimed) => RootVerdict::Mismatch { claimed, derived },
        None => RootVerdict::Unclaimed(derived),
    };
    ReplayOutcome {
        committed,
        skipped,
        verdict,
    }
}

/// Boot a FRESH deterministic demo world at the tape's pinned instant
/// ([`crate::world::demo_world_at`] — fully seeded, the same image the live
/// cockpit boots) and replay the tape onto it. This is THE share-route entry:
/// stateless per link, read-only by construction — a stranger's link never
/// touches a live world, it re-derives its own.
#[cfg(feature = "embedded-executor")]
pub fn replay_fresh(
    tape: &ShareTape,
) -> (crate::world::World, [dregg_cell::CellId; 3], ReplayOutcome) {
    let (mut world, anchors) = crate::world::demo_world_at(tape.timestamp);
    let outcome = replay_onto(&mut world, tape);
    (world, anchors, outcome)
}

// ─── tests ───────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    /// A pinned instant for the deterministic tests (any fixed value works —
    /// determinism is about SHARING it, not about which one).
    const TS: i64 = 1_751_500_800;

    fn full_tape() -> ShareTape {
        ShareTape {
            timestamp: TS,
            tab: Some("inspect-act".to_string()),
            acts: vec![
                ShareAct {
                    cell: "1111".into(),
                    msg: "peek".into(),
                },
                ShareAct {
                    cell: "33".into(),
                    msg: "touch".into(),
                },
            ],
            expected_root: Some([0xAB; 32]),
        }
    }

    #[test]
    fn round_trips_the_empty_tape() {
        let tape = ShareTape {
            timestamp: TS,
            tab: None,
            acts: vec![],
            expected_root: None,
        };
        let frag = encode_fragment(&tape).unwrap();
        assert_eq!(frag, format!("deos1!ts={TS}"));
        assert_eq!(decode_fragment(&frag).unwrap(), tape);
    }

    #[test]
    fn round_trips_the_full_tape_and_the_golden_form_is_stable() {
        let tape = full_tape();
        let frag = encode_fragment(&tape).unwrap();
        // The GOLDEN canonical form — links are forever; if this assertion
        // moves, existing shared links stop decoding. Bump VERSION_TAG instead.
        assert_eq!(
            frag,
            format!(
                "deos1!ts={TS}!tab=inspect-act!root={}!act=1111:peek!act=33:touch",
                "ab".repeat(32)
            )
        );
        assert_eq!(decode_fragment(&frag).unwrap(), tape);
    }

    #[test]
    fn round_trips_hostile_message_strings() {
        // Verbs are data: spaces, unicode, the escape char itself, separators
        // that would break the grammar raw (`!`, `=`, `:`) — all must ride.
        for msg in ["with space", "naïve", "a~b", "a!b=c:d", "ends~"] {
            let tape = ShareTape {
                timestamp: 0,
                tab: Some(msg.to_string()),
                acts: vec![ShareAct {
                    cell: "ee".into(),
                    msg: msg.to_string(),
                }],
                expected_root: None,
            };
            let frag = encode_fragment(&tape).unwrap();
            // Every emitted char is fragment/query-safe: no raw separators leak.
            assert!(
                frag.chars()
                    .all(|c| c.is_ascii_alphanumeric() || "!=:.~-_".contains(c)),
                "unsafe char leaked into fragment: {frag}"
            );
            assert_eq!(decode_fragment(&frag).unwrap(), tape, "msg {msg:?}");
        }
    }

    #[test]
    fn shed_leading_hash_and_any_field_order() {
        let frag = format!("#deos1!act=33:touch!root={}!ts=7", "00".repeat(32));
        let tape = decode_fragment(&frag).unwrap();
        assert_eq!(tape.timestamp, 7);
        assert_eq!(tape.expected_root, Some([0u8; 32]));
        assert_eq!(tape.acts.len(), 1);
    }

    #[test]
    fn refuses_bad_versions_fields_and_values() {
        assert_eq!(
            decode_fragment("deos2!ts=1"),
            Err(ShareLinkError::BadVersion)
        );
        assert_eq!(decode_fragment(""), Err(ShareLinkError::BadVersion));
        assert_eq!(
            decode_fragment("deos1!ts=1!zap=3"),
            Err(ShareLinkError::BadField("zap=3".to_string()))
        );
        assert_eq!(
            decode_fragment("deos1"),
            Err(ShareLinkError::MissingTimestamp)
        );
        assert_eq!(
            decode_fragment("deos1!ts=soon"),
            Err(ShareLinkError::BadTimestamp)
        );
        assert_eq!(
            decode_fragment("deos1!ts=1!ts=2"),
            Err(ShareLinkError::DuplicateField("ts"))
        );
        assert_eq!(
            decode_fragment("deos1!ts=1!root=abcd"),
            Err(ShareLinkError::BadRoot)
        );
        assert_eq!(
            decode_fragment("deos1!ts=1!act=XYZ:peek"),
            Err(ShareLinkError::BadCell("XYZ".to_string()))
        );
        assert_eq!(
            decode_fragment("deos1!ts=1!act=11:pe~zk"),
            Err(ShareLinkError::BadEscape)
        );
        assert_eq!(
            decode_fragment("deos1!ts=1!act=11:pe~F"),
            Err(ShareLinkError::BadEscape)
        );
    }

    #[test]
    fn refuses_over_cap_tapes_on_both_ends() {
        // Decode: MAX_ACTS + 1 acts.
        let mut frag = String::from("deos1!ts=1");
        for _ in 0..=MAX_ACTS {
            frag.push_str("!act=11:peek");
        }
        assert!(matches!(
            decode_fragment(&frag),
            Err(ShareLinkError::TooManyActs { .. })
        ));
        // Encode: the same tape refuses to mint.
        let tape = ShareTape {
            timestamp: 1,
            tab: None,
            acts: vec![
                ShareAct {
                    cell: "11".into(),
                    msg: "peek".into()
                };
                MAX_ACTS + 1
            ],
            expected_root: None,
        };
        assert!(matches!(
            encode_fragment(&tape),
            Err(ShareLinkError::TooManyActs { .. })
        ));
        // Length cap.
        let long = format!("deos1!ts=1!tab={}", "a".repeat(MAX_FRAGMENT_LEN));
        assert!(matches!(
            decode_fragment(&long),
            Err(ShareLinkError::TooLong { .. })
        ));
    }

    #[test]
    fn share_url_is_base_hash_fragment() {
        let tape = ShareTape {
            timestamp: 9,
            tab: None,
            acts: vec![],
            expected_root: None,
        };
        assert_eq!(
            share_url("https://x.test/deos-viewer/", &tape).unwrap(),
            "https://x.test/deos-viewer/#deos1!ts=9"
        );
    }

    // ── the determinism teeth (the whole point of the format) ───────────────

    /// Two fresh boots at the SAME pinned instant replaying the SAME tape must
    /// derive the SAME canonical ledger root — the property the share URL's
    /// `root` claim rides on.
    #[cfg(feature = "embedded-executor")]
    #[test]
    fn same_tape_same_instant_same_root() {
        // Resolve a real act target dynamically (never hardcode an id): the
        // demo user cell's hex prefix, off a probe boot.
        let (probe, anchors) = crate::world::demo_world_at(TS);
        let user_prefix = hex::encode(anchors[2].as_bytes())[..8].to_string();
        drop(probe);

        let tape = ShareTape {
            timestamp: TS,
            tab: None,
            acts: vec![ShareAct {
                cell: user_prefix,
                msg: "peek".into(),
            }],
            expected_root: None,
        };
        let (_, _, a) = replay_fresh(&tape);
        let (_, _, b) = replay_fresh(&tape);
        let (RootVerdict::Unclaimed(ra), RootVerdict::Unclaimed(rb)) = (&a.verdict, &b.verdict)
        else {
            panic!("no root claim was made — verdicts must be Unclaimed");
        };
        assert_eq!(ra, rb, "two fresh boots diverged under one pinned instant");
    }

    /// Bake the derived root back into the tape as the claim → the verdict is
    /// Match; corrupt the claim → the verdict is honestly Mismatch.
    #[cfg(feature = "embedded-executor")]
    #[test]
    fn root_claim_matches_and_mismatch_is_surfaced() {
        let mut tape = ShareTape {
            timestamp: TS,
            tab: None,
            acts: vec![],
            expected_root: None,
        };
        let (_, _, first) = replay_fresh(&tape);
        let RootVerdict::Unclaimed(root) = first.verdict else {
            panic!("no claim yet");
        };

        tape.expected_root = Some(root);
        let (_, _, second) = replay_fresh(&tape);
        assert!(matches!(second.verdict, RootVerdict::Match(r) if r == root));

        let mut forged = root;
        forged[0] ^= 0xFF;
        tape.expected_root = Some(forged);
        let (_, _, third) = replay_fresh(&tape);
        assert!(matches!(
            third.verdict,
            RootVerdict::Mismatch { claimed, derived } if claimed == forged && derived == root
        ));
    }

    /// An act that resolves no cell is SKIPPED IN-BAND (recorded, surfaced) —
    /// and the world still derives a root (the honest partial reconstruction).
    #[cfg(feature = "embedded-executor")]
    #[test]
    fn unresolvable_acts_skip_in_band() {
        let tape = ShareTape {
            timestamp: TS,
            tab: None,
            acts: vec![ShareAct {
                // 64 hex chars of f — a full-width id that matches nothing.
                cell: "f".repeat(64),
                msg: "peek".into(),
            }],
            expected_root: None,
        };
        let (_, _, outcome) = replay_fresh(&tape);
        assert_eq!(outcome.committed, 0);
        assert_eq!(outcome.skipped.len(), 1);
        assert!(outcome.skipped[0].1.contains("no cell matches"));
    }
}
