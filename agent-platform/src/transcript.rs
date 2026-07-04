//! **The SSE wire for a grain**: the drive's reason→act→observe transcript as a
//! `text/event-stream` body (meta/step/done), mirroring the frame shape of
//! the attach portal SSE stream.
//!
//! ## The honest streaming approach
//! `AgentPlatform::drive` / `drive_live` run **synchronously** — a call returns
//! only after the goal has run to completion, its per-step outcomes committed to
//! the session's history. So this transcript is an honest **replay** of the
//! just-completed drive(s): it walks the session's committed [`GoalReport`] steps
//! (`crate::AgentPlatform` accumulates one per goal) and emits one `step` frame per
//! [`LiveStep`] — each admitted/refused action, its cap-gate verdict, and its
//! receipt/tool summary — bracketed by a `meta` header and a `done` bound. This is
//! exactly attach's `transcript_stream`: it replays a completed session's recorded
//! transcript, not a genuinely-incremental push. A live "stream each step AS it
//! runs" would need the goal loop to publish to a per-grain channel the SSE body
//! drains; the frame SHAPE + wire here are the real half, ready for that backend.
//!
//! Frames:
//! - `event: meta` — the grain host · latest goal · budget · asset · caps · #goals.
//! - `event: step` — one [`LiveStep`] (the reason→act→observe line + its receipt).
//! - `event: done` — the final budget bound + the admitted/refused/receipt tallies.

use dregg_agent::session::Session;
use serde::Serialize;

/// The opening `meta` frame payload — the grain/session header.
#[derive(Clone, Debug, Serialize)]
pub struct MetaEvent {
    /// The grain host (its stable id).
    pub host: String,
    /// The most-recent natural-language goal driven (empty if none yet).
    pub goal: String,
    /// The budget ceiling (the hard bound on the whole session).
    pub budget: i64,
    /// The asset the budget is denominated in.
    pub asset: String,
    /// The granted cap bundle (display form).
    pub caps: Vec<String>,
    /// How many goals the grain has run (the transcript spans all of them).
    pub goals: usize,
}

/// The closing `done` frame payload — the final bound + tallies.
#[derive(Clone, Debug, Serialize)]
pub struct DoneEvent {
    /// The budget ceiling.
    pub budget: i64,
    /// Total consumed across the session.
    pub consumed: i64,
    /// Un-drawn headroom (the could-have bound).
    pub headroom: i64,
    /// Admitted (receipted) actions.
    pub admitted: u64,
    /// Cap-refused actions (outside the bundle).
    pub cap_refused: u64,
    /// Budget-refused actions (over the ceiling).
    pub budget_refused: u64,
    /// The sealed receipt count.
    pub receipts: usize,
}

/// Encode one SSE frame: `event: <name>\ndata: <json>\n\n`. `data` is single-line
/// JSON (serde_json emits no newlines), so the frame is one well-formed event.
pub fn sse_frame(event: &str, data_json: &str) -> String {
    format!("event: {event}\ndata: {data_json}\n\n")
}

/// The whole `text/event-stream` body for a grain: the `meta` frame, one `step`
/// frame per committed transcript step across every goal, then the `done` frame.
pub fn transcript_stream(host: &str, session: &Session) -> String {
    let mut out = String::new();

    let latest_goal = session
        .history()
        .last()
        .map(|g| g.goal.clone())
        .unwrap_or_default();
    let meta = MetaEvent {
        host: host.to_string(),
        goal: latest_goal,
        budget: session.budget(),
        asset: session.asset().to_string(),
        caps: session.caps().to_vec(),
        goals: session.goal_count(),
    };
    out.push_str(&sse_frame(
        "meta",
        &serde_json::to_string(&meta).unwrap_or_default(),
    ));

    // One `step` frame per committed LiveStep, in order, across all goals — each
    // admitted/refused action + its receipt/tool summary, as it landed.
    for goal in session.history() {
        for step in &goal.steps {
            out.push_str(&sse_frame(
                "step",
                &serde_json::to_string(step).unwrap_or_default(),
            ));
        }
    }

    let report = session.report();
    let done = DoneEvent {
        budget: report.budget,
        consumed: report.consumed,
        headroom: report.headroom,
        admitted: report.admitted,
        cap_refused: report.cap_refused,
        budget_refused: report.budget_refused,
        receipts: report.receipts.len(),
    };
    out.push_str(&sse_frame(
        "done",
        &serde_json::to_string(&done).unwrap_or_default(),
    ));

    out
}
