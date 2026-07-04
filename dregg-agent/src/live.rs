//! `live` — the **flexible live run**: the `run.json` artifact a real adaptive
//! agent emits, and its host-untrusted re-witness.
//!
//! The agent takes an **arbitrary natural-language goal** + a budget + a cap
//! bundle and runs a real reason → act → observe loop on a live model: the model
//! decides the next tool call, the run loop cap-gates + meters + receipts it, runs
//! it for real, and feeds the result back. A judge can hand it a *different* goal
//! and watch it adapt — that is the proof it is not scripted.
//!
//! [`LiveRun`] is the whole record (goal · model · the granted bundle · the
//! receipt chain · the narrated transcript); [`verify_live`] re-witnesses it
//! offline (chain intact + signed, the spend bound holds, the sub-agent chain
//! too), so `dregg-agent verify run.json` needs only the file. A tampered
//! line breaks the ed25519 receipt signature.

use serde::{Deserialize, Serialize};

use crate::agent::{ActionOutcome, AgentRunReport, verify_agent_run};

/// The serde default for [`LiveRun::brain_mode`]: a record written before the field
/// existed predates the recorded-brain provenance marker, so it is treated as `"live"`.
fn default_brain_mode() -> String {
    "live".to_string()
}

/// One narrated step of the reason → act → observe loop (derived from the signed
/// run log + receipts — every line traces to a receipt or a refusal).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LiveStep {
    /// The 1-based step ordinal.
    pub n: u64,
    /// The action label the model decided (`git_clone:…`, `shell:…`, `spend:…`).
    pub action: String,
    /// `admitted` / `cap-refused: <cap>` / `budget-refused (headroom N)`.
    pub outcome: String,
    /// For an admitted tool call: the real tool verdict summary (truncated).
    pub tool_summary: Option<String>,
    /// The budget units this step drew (0 for a refusal).
    pub cost: i64,
}

/// The whole live run — the `run.json` a non-witness re-verifies offline.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LiveRun {
    /// The natural-language goal the agent was given.
    pub goal: String,
    /// The model id that drove it (e.g. `nvidia/llama-3.3-nemotron-super-49b-v1`).
    pub model: String,
    /// The provider endpoint (no key — the key never enters the record).
    pub endpoint: String,
    /// The **brain provenance** of this run: `"live"` (the model was actually called
    /// over HTTP) or `"replay"` (the model *decisions* came from a recorded
    /// transcript). The TOOLS execute for real in either case, so the receipt chain
    /// and [`verify_live`] hold regardless of provenance — but a `--replay` artifact
    /// still stamps the live default `model`/`endpoint`, so this field is what makes
    /// `run.json` honest *standalone*: a judge reading the file alone (not the
    /// ephemeral `[mode] REPLAY …` stdout banner) can tell a recorded run from a live
    /// one. Serde-defaults to `"live"` for older artifacts written before this field.
    #[serde(default = "default_brain_mode")]
    pub brain_mode: String,
    /// How the budget was funded — an honest source note (operator allowance, or a
    /// real Stripe test PaymentIntent when a test key is present).
    pub funding: String,
    /// The budget ceiling, in cents.
    pub budget_cents: i64,
    /// The granted cap bundle (display form; a resource prefix renders with `*`).
    pub caps: Vec<String>,
    /// The workdir the operator tools were confined to.
    pub workdir: String,
    /// The main agent run — one re-witnessable receipt chain.
    pub run: AgentRunReport,
    /// An optional forked sub-agent run (the SCALE / attenuation demo).
    pub subagent_run: Option<AgentRunReport>,
    /// The narrated reason → act → observe transcript.
    pub transcript: Vec<LiveStep>,
}

impl LiveRun {
    /// The real tool calls the agent made (admitted ops/invokes), for a quick
    /// "what did it actually do?" rollup.
    pub fn tool_calls(&self) -> usize {
        self.run.receipts.len()
    }
}

/// Build the narrated transcript from a run report's signed log + receipts. Every
/// admitted step is paired with its receipt (verdict + cost) in order.
pub fn transcript_of(report: &AgentRunReport) -> Vec<LiveStep> {
    transcript_of_slices(&report.log, &report.receipts)
}

/// Build the narrated transcript from a `(log, receipts)` slice pair — the
/// per-goal **delta** form a [`crate::session::Session`] uses to narrate only the
/// steps a single typed goal added (slice both vectors from the marks recorded
/// before the goal ran; the admitted entries in the log slice pair 1:1 with the
/// receipt slice, in order).
pub fn transcript_of_slices(
    log: &[crate::agent::ActionRecord],
    receipts: &[crate::agent::AgentReceipt],
) -> Vec<LiveStep> {
    let mut steps = Vec::new();
    let mut ri = 0usize;
    for (i, rec) in log.iter().enumerate() {
        let (outcome, tool_summary, cost) = match &rec.outcome {
            ActionOutcome::Admitted => {
                let r = receipts.get(ri);
                ri += 1;
                (
                    "admitted".to_string(),
                    r.and_then(|r| r.tool_summary.clone()),
                    r.map(|r| r.cost).unwrap_or(0),
                )
            }
            ActionOutcome::CapRefused { cap } => {
                (format!("REFUSED — outside the cap bundle ({cap})"), None, 0)
            }
            ActionOutcome::BudgetRefused { headroom } => (
                format!("REFUSED in-band — over budget (headroom {headroom}); no effect"),
                None,
                0,
            ),
            ActionOutcome::TurnRefused { reason } => (
                format!("REFUSED by the executor (R2 host-side caveat: {reason}); no effect"),
                None,
                0,
            ),
        };
        steps.push(LiveStep {
            n: (i + 1) as u64,
            action: rec.action.clone(),
            outcome,
            tool_summary,
            cost,
        });
    }
    steps
}

/// What re-witnessing a [`LiveRun`] confirmed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LiveVerified {
    /// Admitted actions in the main chain.
    pub actions: usize,
    /// Budget consumed (≤ ceiling).
    pub consumed: i64,
    /// Un-drawn headroom (the could-have bound).
    pub headroom: i64,
    /// The budget ceiling.
    pub budget: i64,
    /// Admitted actions in the sub-agent chain (0 if none).
    pub subagent_actions: usize,
}

/// **Re-witness a live run offline, trusting no host:** the main receipt chain is
/// signed + unbroken + tamper-evident; consumed stays at/under the ceiling and
/// agrees with the chain tip; the sub-agent chain (if any) re-witnesses too.
pub fn verify_live(run: &LiveRun) -> Result<LiveVerified, String> {
    let main = verify_agent_run(&run.run).map_err(|e| format!("agent run: {e}"))?;
    if run.run.budget != run.budget_cents {
        return Err(format!(
            "budget mismatch: report {} != funded {}",
            run.run.budget, run.budget_cents
        ));
    }
    let subagent_actions = match &run.subagent_run {
        Some(sub) => {
            verify_agent_run(sub)
                .map_err(|e| format!("sub-agent run: {e}"))?
                .actions
        }
        None => 0,
    };
    Ok(LiveVerified {
        actions: main.actions,
        consumed: main.consumed,
        headroom: main.headroom,
        budget: main.budget,
        subagent_actions,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::agent::{AgentAction, AgentCloud, AgentSpec, PlannedBrain, ToolCall};
    use crate::toolkit::Toolkit;
    use crate::tools::{OperatorTools, ShellOut};
    use std::path::Path;

    fn op(tool: &str, kv: &[(&str, &str)]) -> AgentAction {
        AgentAction::Op(ToolCall::new(
            tool,
            kv.iter().map(|(k, v)| (k.to_string(), v.to_string())),
        ))
    }

    #[test]
    fn a_live_run_record_re_witnesses_and_a_tamper_is_caught() {
        let wd = std::env::temp_dir().join(format!("dregg-live-{}", std::process::id()));
        std::fs::create_dir_all(&wd).unwrap();
        let cloud = AgentCloud::from_seed([90u8; 32]);
        let handle = cloud
            .deploy(&AgentSpec::new("agent:live", 100).with_shell())
            .unwrap();
        let toolkit =
            OperatorTools::new(Toolkit::new(), &wd).with_shell(|cmd: &str, _cwd: &Path| {
                Ok(ShellOut {
                    exit: 0,
                    stdout: format!("ok: {cmd}"),
                    stderr: String::new(),
                    new_cwd: None,
                })
            });
        let report = cloud.run_with_toolkit(
            &handle,
            &mut PlannedBrain::new(vec![op("shell", &[("cmd", "echo hi")])]),
            &toolkit,
        );
        let mut run = LiveRun {
            goal: "say hi".into(),
            model: "test".into(),
            endpoint: "test".into(),
            brain_mode: "live".into(),
            funding: "operator allowance".into(),
            budget_cents: 100,
            caps: handle.caps.clone(),
            workdir: wd.to_string_lossy().into(),
            transcript: transcript_of(&report),
            run: report,
            subagent_run: None,
        };
        let v = verify_live(&run).expect("the live run re-witnesses");
        assert_eq!(v.actions, 1);
        assert_eq!(run.transcript.len(), 1);
        assert_eq!(run.transcript[0].outcome, "admitted");

        // Tamper a receipt verdict → BadSignature on re-witness.
        run.run.receipts[0].tool_ok = Some(false);
        assert!(verify_live(&run).is_err(), "the tamper is caught");
        std::fs::remove_dir_all(&wd).ok();
    }

    #[test]
    fn brain_mode_is_honest_standalone_and_back_compatible() {
        // An artifact written before the field existed (no `brain_mode`) parses as
        // "live" — the serde default — so it round-trips without loss.
        let legacy = r#"{
            "goal":"g","model":"m","endpoint":"e","funding":"f","budget_cents":0,
            "caps":[],"workdir":"w",
            "run":{"agent":"a","asset":"USD-CENTS","budget":0,"consumed":0,
                   "headroom":0,"admitted":0,"cap_refused":0,"budget_refused":0,
                   "receipts":[],"log":[],
                   "signer":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
                   "cells":{}},
            "subagent_run":null,"transcript":[]
        }"#;
        let parsed: LiveRun = serde_json::from_str(legacy).expect("legacy run parses");
        assert_eq!(parsed.brain_mode, "live", "missing field defaults to live");

        // A recorded-brain run is stamped "replay" and survives a round-trip, so the
        // provenance is honest even when the file is read standalone.
        let replayed = LiveRun {
            brain_mode: "replay".into(),
            ..parsed
        };
        let json = serde_json::to_string(&replayed).expect("serializes");
        assert!(json.contains("\"brain_mode\":\"replay\""));
        let back: LiveRun = serde_json::from_str(&json).expect("re-parses");
        assert_eq!(back.brain_mode, "replay");
    }
}
