//! `dregg-agent` — the **flexible, live, bounded operator agent** CLI.
//!
//! ```text
//!   dregg-agent run --goal "<natural-language goal>" [--budget N] [--caps …]
//!                   [--brain nemotron|hermes|hermes-cli]
//!                   [--workdir DIR] [--model M] [--base URL]
//!                   [--llm-base URL] [--llm-model M] [--step-cap N]
//!                   [--out run.json] [--record resp.json | --replay resp.json] [--no-scale]
//!   dregg-agent verify <run.json> [--tamper]
//! ```
//!
//! `--brain hermes` drives the **actual Nous Hermes model** over the Nous Portal
//! (`http://127.0.0.1:8645/v1`, model `hermes-agent`, bearer `~/.nousportalkey` /
//! `NOUS_PORTAL_KEY`). `--brain hermes-cli` drives the **real `hermes` CLI** as the
//! confined harness — it reasons with its own installed skills (incl. the real
//! Stripe Skills) while dregg intercepts each skill-call through the
//! cap-gate + budget + receipt. Both go live the moment the Nous Portal key / the
//! `hermes` CLI are present; offline they run a faithful recorded transport.
//!
//! `run` gives a live model an arbitrary goal + a budget + a cap bundle, and runs
//! a real reason → act → observe loop: the model decides the next tool call, the
//! run loop **cap-gates + meters + receipts** it, runs it for REAL (a real shell /
//! fs / http / git, or a budget-gated spend), feeds the result back, and repeats
//! until the model finishes or the budget / step-cap bounds it. Hand it a
//! *different* `--goal` and it genuinely adapts — that is the proof it is not
//! scripted. It writes `run.json`; `verify` re-witnesses the whole run offline
//! (chain + bound), host untrusted; `--tamper` flips one line and it is caught
//! (`BadSignature`). The default model is a confirmed-live NVIDIA Nemotron.

use std::process::ExitCode;

use dregg_agent::live::{LiveRun, verify_live};

/// The default live model: confirmed to do native OpenAI `tool_calls` on the
/// NVIDIA NIM endpoint for this account (Ultra/70b are listed but 404 on
/// inference here; super-49b is the working agentic model).
#[cfg(feature = "live-brain")]
const DEFAULT_MODEL: &str = "nvidia/llama-3.3-nemotron-super-49b-v1";
/// The NVIDIA NIM OpenAI-compatible base.
#[cfg(feature = "live-brain")]
const DEFAULT_BASE: &str = "https://integrate.api.nvidia.com/v1";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("run") => cmd_run(&args[1..]),
        Some("verify") => cmd_verify(&args[1..]),
        Some("session") => repl::cmd_session(&args[1..], repl::Mode::Session),
        Some("attach") => repl::cmd_session(&args[1..], repl::Mode::Attach),
        Some("-h") | Some("--help") | None => {
            usage();
            ExitCode::SUCCESS
        }
        Some(other) => {
            eprintln!("unknown command `{other}`\n");
            usage();
            ExitCode::FAILURE
        }
    }
}

fn usage() {
    println!(
        "dregg-agent — a flexible, live, bounded operator agent\n\n\
         USAGE:\n\
         \x20 dregg-agent run --goal \"<goal>\" [--budget N] [--caps a,b,…] [--workdir DIR]\n\
         \x20                 [--brain nemotron|hermes|hermes-cli]\n\
         \x20                 [--model M] [--base URL] [--llm-model M] [--llm-base URL]\n\
         \x20                 [--step-cap N] [--out run.json]\n\
         \x20                 [--record resp.json | --replay resp.json] [--no-scale]\n\
         \x20 dregg-agent session [--account ID] [--budget N] [--caps a,b,…] [--workdir DIR]\n\
         \x20                     [--brain nemotron|hermes] [--model M] [--base URL]\n\
         \x20                     [--replay resp.json] [--out session.json] [--hosted]\n\
         \x20 dregg-agent attach  --account ID [--budget N] [--caps a,b,…] [--workdir DIR]\n\
         \x20                     [--brain …] [--replay resp.json] [--os-isolation]\n\
         \x20                     (the SSH forced-command target; HOSTED — no raw shell)\n\
         \x20 dregg-agent verify <run.json> [--tamper]\n\n\
         SESSION / ATTACH:\n\
         \x20 A persistent, budget-bounded, cap-gated agent session you DRIVE goal by\n\
         \x20 goal. Type a goal → it runs a real reason→act→observe loop (cap-gated ·\n\
         \x20 metered · receipted) → the budget draws down + the receipt chain\n\
         \x20 accumulates across goals. REPL commands: :status :caps :verify :history\n\
         \x20 :help :quit. `attach` is the same REPL scoped to one account — the target\n\
         \x20 an SSH authorized_keys `command=` drops a connecting user into.\n\n\
         BRAIN:\n\
         \x20 nemotron   (default) NVIDIA Nemotron over its OpenAI-compatible endpoint\n\
         \x20 hermes     the actual Nous Hermes model over the Nous Portal proxy\n\
         \x20            (http://127.0.0.1:8645/v1, model hermes-agent; key ~/.nousportalkey)\n\
         \x20 hermes-cli the real `hermes` CLI as the confined harness (its own skills)\n\n\
         CAPS (comma-separated): shell, fs, git:HOST, http:HOST, run_tests,\n\
         \x20                     provision:PROVIDER (Stripe Projects skill),\n\
         \x20                     pay:VENDOR (Stripe Link skill), spend (pay any vendor),\n\
         \x20                     cell:/path  (each is a per-tool/per-resource grant)\n\
         \x20  `shell` is LOCAL-ONLY: a hosted session (attach, or session --hosted)\n\
         \x20  refuses it — a raw shell can read the host's operator keys past the\n\
         \x20  env-scrub. Restore it on a hosted box with per-tenant OS isolation.\n\n\
         The agent runs a real reason→act→observe loop on a live model; every tool\n\
         call is cap-gated + metered + receipted. verify re-witnesses run.json\n\
         offline; --tamper flips a line and it is caught (BadSignature)."
    );
}

fn flag<'a>(args: &'a [String], name: &str) -> Option<&'a str> {
    args.iter()
        .position(|a| a == name)
        .and_then(|i| args.get(i + 1))
        .map(String::as_str)
}

fn has(args: &[String], name: &str) -> bool {
    args.iter().any(|a| a == name)
}

// ─────────────────────────────── verify (std-only) ───────────────────────────

fn cmd_verify(args: &[String]) -> ExitCode {
    let Some(path) = args.iter().find(|a| !a.starts_with("--")) else {
        eprintln!("usage: dregg-agent verify <run.json> [--tamper]");
        return ExitCode::FAILURE;
    };
    let tamper = has(args, "--tamper");
    let raw = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("cannot read {path}: {e}");
            return ExitCode::FAILURE;
        }
    };
    let mut run: LiveRun = match serde_json::from_str(&raw) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("cannot parse {path}: {e}");
            return ExitCode::FAILURE;
        }
    };

    rule();
    if tamper {
        println!("  THE TEETH — flip one receipted line; the audit catches it");
    } else {
        println!("  PROVE — re-witness the whole run offline, trusting no host");
    }
    rule();
    println!();

    if tamper {
        // Prefer a Stripe-pay receipt (the "I barely paid" forgery — a real dollar
        // amount bound into the receipt); else a legacy spend; else any receipt.
        let idx = run
            .run
            .receipts
            .iter()
            .position(|r| r.action.starts_with("stripe_pay"))
            .or_else(|| {
                run.run
                    .receipts
                    .iter()
                    .position(|r| r.action.starts_with("spend:"))
            })
            .or(if run.run.receipts.is_empty() {
                None
            } else {
                Some(0)
            });
        match idx {
            Some(i) => {
                let r = &mut run.run.receipts[i];
                let was = r.cost;
                // Guaranteed-different value (so the body hash actually moves).
                r.cost = if was == 1 { 999 } else { 1 };
                println!(
                    "[tamper] flipped {} cost: {was}¢ → {}¢ (\"it barely spent anything\")\n",
                    r.action, r.cost
                );
            }
            None => println!("[tamper] no receipt to flip (the model committed nothing)\n"),
        }
    }

    match verify_live(&run) {
        Ok(v) => {
            println!("   GOAL: {}", run.goal);
            // Surface the brain provenance so a reader knows whether the model was
            // actually called (live) or its decisions were replayed from a recording.
            // The tools ran for real either way — this only marks the model provenance.
            if run.brain_mode == "replay" {
                println!(
                    "   • brain    REPLAY (recorded model decisions; tools ran for real) — model {} @ {}",
                    run.model, run.endpoint
                );
            } else {
                println!(
                    "   • brain    live — model {} @ {}",
                    run.model, run.endpoint
                );
            }
            println!(
                "   ✓ chain    {} action(s), signed + unbroken + tamper-evident",
                v.actions
            );
            println!(
                "   ✓ bound    consumed {}¢ ≤ ceiling {}¢; headroom {}¢",
                v.consumed, v.budget, v.headroom
            );
            if run.subagent_run.is_some() {
                println!(
                    "   ✓ scale    sub-agent chain re-witnessed — {} action(s)",
                    v.subagent_actions
                );
            }
            println!("\n   VERDICT: ✓ the live agent run re-verifies offline.\n");
            ExitCode::SUCCESS
        }
        Err(e) => {
            println!("   ✗ REJECTED: {e}");
            println!("\n   VERDICT: ✗ the audit caught it — the proof does not lie.\n");
            // A caught tamper is the INTENDED outcome of --tamper.
            if tamper {
                ExitCode::SUCCESS
            } else {
                ExitCode::FAILURE
            }
        }
    }
}

fn rule() {
    println!("════════════════════════════════════════════════════════════════════");
}

// ─────────────────────────────── run (needs live-brain) ──────────────────────

#[cfg(not(feature = "live-brain"))]
fn cmd_run(_args: &[String]) -> ExitCode {
    eprintln!(
        "`run` drives a LIVE model + real http and needs the `live-brain` feature.\n\
         Rebuild:  cargo build -p dregg-agent --bin dregg-agent --features live-brain"
    );
    ExitCode::FAILURE
}

#[cfg(feature = "live-brain")]
fn cmd_run(args: &[String]) -> ExitCode {
    live::run(args)
}

#[cfg(feature = "live-brain")]
mod live {
    use super::*;
    use std::path::{Path, PathBuf};
    use std::time::Duration;

    use dregg_agent::agent::{
        AgentAction, AgentCloud, AgentHandle, AgentRunReport, AgentSpec, PlannedBrain, ToolCall, op,
    };
    use dregg_agent::brain::{
        LiveOpenAICompatCaller, OpenAICompatBrain, OpenAICompatCaller, ProviderKey,
    };
    use dregg_agent::harness::{HarnessBrain, MockHarness};
    use dregg_agent::hermes;
    use dregg_agent::live::{LiveRun, transcript_of};
    use dregg_agent::stripe_skills;
    use dregg_agent::toolkit::Toolkit;
    use dregg_agent::tools::{HttpResp, OperatorTools};
    use serde_json::Value;

    /// The selected brain profile (`--brain`).
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum BrainKind {
        /// NVIDIA Nemotron over its OpenAI-compatible endpoint (the default).
        Nemotron,
        /// The actual Nous Hermes model over the Nous Portal proxy.
        Hermes,
        /// The real `hermes` CLI as the confined harness (its own skills).
        HermesCli,
    }

    impl BrainKind {
        fn parse(s: &str) -> Option<BrainKind> {
            match s {
                "nemotron" | "nvidia" => Some(BrainKind::Nemotron),
                "hermes" | "hermes-portal" | "nous" => Some(BrainKind::Hermes),
                "hermes-cli" | "hermes-harness" => Some(BrainKind::HermesCli),
                _ => None,
            }
        }
    }

    /// A real, default-demoable goal that exercises git + shell + fs + http + the
    /// two real **Stripe Skills** (provision a SaaS, pay a vendor) — all real,
    /// ~30-60s, network-light. The Stripe legs run against the recorded transport
    /// offline and the live CLIs the moment a test key + the CLIs are present.
    const DEFAULT_GOAL: &str = "Clone the small repo https://github.com/octocat/Hello-World \
        into your workdir, list the files you cloned and read the README, then GET \
        https://api.github.com/repos/octocat/Hello-World and report the repo's description. \
        Then provision your own database with stripe_provision (provider neon, service \
        postgres, amount_cents 1900) and pay 50 cents to the vendor 'openai' via stripe_pay \
        (memo: inference) for the work you did. Stay under budget and call finish with a \
        one-line summary of what you found.";

    const DEFAULT_CAPS: &str =
        "shell,fs,git:github.com,http:api.github.com,provision:neon,pay:openai";

    pub fn run(args: &[String]) -> ExitCode {
        let goal = flag(args, "--goal").unwrap_or(DEFAULT_GOAL).to_string();
        let budget: i64 = flag(args, "--budget")
            .and_then(|s| s.parse().ok())
            .unwrap_or(500);
        let caps_str = flag(args, "--caps").unwrap_or(DEFAULT_CAPS).to_string();

        // The brain profile selects the default endpoint/model + the key source.
        let brain_kind = match flag(args, "--brain") {
            Some(s) => match BrainKind::parse(s) {
                Some(k) => k,
                None => {
                    eprintln!("unknown --brain `{s}` (use: nemotron | hermes | hermes-cli)");
                    return ExitCode::FAILURE;
                }
            },
            None => BrainKind::Nemotron,
        };
        // Per-brain endpoint/model defaults; --model/--base (or --llm-model/--llm-base
        // aliases) override. `hermes` defaults to the Nous Portal + the Hermes model.
        let (default_base, default_model) = match brain_kind {
            BrainKind::Hermes => (
                dregg_agent::brain::NOUS_PORTAL_BASE,
                dregg_agent::brain::HERMES_PORTAL_MODEL,
            ),
            _ => (DEFAULT_BASE, DEFAULT_MODEL),
        };
        let model = flag(args, "--model")
            .or_else(|| flag(args, "--llm-model"))
            .unwrap_or(default_model)
            .to_string();
        let base = flag(args, "--base")
            .or_else(|| flag(args, "--llm-base"))
            .unwrap_or(default_base)
            .to_string();
        let step_cap: u64 = flag(args, "--step-cap")
            .and_then(|s| s.parse().ok())
            .unwrap_or(16);
        let out = flag(args, "--out").unwrap_or("run.json").to_string();
        let scale = !has(args, "--no-scale");

        // For a FAITHFUL film replay, reuse the recorded run's workdir by default
        // (the model's tool calls may carry absolute paths tied to it; a different
        // workdir would correctly cap-refuse them). An explicit --workdir overrides.
        let replay_arg = flag(args, "--replay").map(String::from);
        let recorded_workdir = replay_arg
            .as_deref()
            .and_then(|p| load_record(p).ok())
            .map(|r| r.workdir);
        let workdir = flag(args, "--workdir")
            .map(PathBuf::from)
            .or_else(|| {
                recorded_workdir
                    .filter(|s| !s.is_empty())
                    .map(PathBuf::from)
            })
            .unwrap_or_else(|| {
                std::env::temp_dir().join(format!("dregg-agent-wd-{}", std::process::id()))
            });
        if let Err(e) = std::fs::create_dir_all(&workdir) {
            eprintln!("cannot create workdir {}: {e}", workdir.display());
            return ExitCode::FAILURE;
        }
        let workdir = workdir.canonicalize().unwrap_or(workdir);
        let workdir_s = workdir.to_string_lossy().to_string();

        // Build the cap bundle + the advertised tool lists from --caps.
        let Bundle {
            mut spec,
            services,
            op_tools,
            cells,
        } = match parse_caps(&caps_str, "agent:operator", budget, &workdir_s) {
            Ok(b) => b,
            Err(e) => {
                eprintln!("bad --caps: {e}");
                return ExitCode::FAILURE;
            }
        };
        // The budget is denominated in cents; one op costs 1¢, a spend costs its amount.
        spec.asset = "USD-CENTS".into();

        let cloud = AgentCloud::new();
        let handle = match cloud.deploy(&spec) {
            Ok(h) => h,
            Err(e) => {
                eprintln!("deploy failed: {e}");
                return ExitCode::FAILURE;
            }
        };

        rule();
        println!("  dregg-agent — a flexible, live, bounded operator agent");
        rule();
        println!();
        println!("  GOAL    {goal}");
        match brain_kind {
            BrainKind::Nemotron => {
                println!("  BRAIN   nemotron (model)\n  MODEL   {model} @ {base}")
            }
            BrainKind::Hermes => println!(
                "  BRAIN   hermes (Nous Hermes model, direct)\n  MODEL   {model} @ {base}\n  HERMES  {}",
                hermes::portal_status_line()
            ),
            BrainKind::HermesCli => println!(
                "  BRAIN   hermes-cli (the REAL hermes CLI as the confined harness, its own skills)\n  HERMES  {}",
                hermes::hermes_cli_status_line()
            ),
        }
        println!("  BUDGET  {budget}¢   STEP-CAP {step_cap}   WORKDIR {workdir_s}");
        println!("  CAPS    {}", handle.caps.join("  ·  "));

        // Funding (honest): the budget cell is the spend ceiling; the Stripe Skills
        // (provision + pay) draw from it. Live the moment the CLIs + a test key land.
        let funding = format!(
            "operator budget of {budget}¢ (the spend ceiling the Stripe Skills draw from) · \
             Stripe Skills: {}",
            stripe_skills::status_line()
        );
        println!("  FUNDING {funding}");
        println!();

        // The real operator toolkit: real shell (timeout + cwd), real http
        // (reqwest), real fs (std, workdir-confined), git via the shell runner,
        // plus the REAL **Stripe Skills** (stripe_provision + stripe_pay) — the live
        // CLIs when present, the recorded transport offline. detect() picks.
        let timeout = Duration::from_secs(60);
        let toolkit = OperatorTools::new(Toolkit::new(), &workdir)
            .with_shell(move |cmd, cwd| dregg_agent::tools::real_shell(cmd, cwd, timeout))
            .with_http(real_http)
            .with_stripe_skills_boxed(stripe_skills::detect());

        // The brain: a live model over native tool_calls (confirmed), driving the
        // reason→act→observe loop. Replay re-feeds a recorded transcript.
        let replay = replay_arg;
        let record = flag(args, "--record").map(String::from);

        println!(
            "──[ reason → act → observe ]── (live; each step is cap-gated · metered · receipted)\n"
        );

        let report = if brain_kind == BrainKind::HermesCli {
            // (b) THE AUTHENTIC PATH: the real `hermes` CLI as the confined harness.
            run_hermes_cli(&cloud, &handle, &goal, &toolkit, step_cap)
        } else if let Some(rp) = &replay {
            let responses = match load_record(rp) {
                Ok(r) => r.responses,
                Err(e) => {
                    eprintln!("cannot load replay {rp}: {e}");
                    return ExitCode::FAILURE;
                }
            };
            println!(
                "  [mode] REPLAY of a recorded brain ({} responses) — tools execute for real\n",
                responses.len()
            );
            let caller = dregg_agent::brain::RecordedOpenAICaller::new(responses);
            let mut brain = make_brain(
                &goal,
                &services,
                &cells,
                &op_tools,
                ProviderKey::unauthenticated(),
                &base,
                &model,
                caller,
                step_cap,
            );
            cloud.run_with_toolkit(&handle, &mut brain, &toolkit)
        } else {
            // (a) the model brain: nemotron, or the actual Hermes model over the Portal.
            let key = match model_key(brain_kind) {
                Some(k) => k,
                None => {
                    eprintln!("{}", key_help(brain_kind));
                    return ExitCode::FAILURE;
                }
            };
            let caller = TeeCaller::new(LiveOpenAICompatCaller::new());
            let mut brain = make_brain(
                &goal, &services, &cells, &op_tools, key, &base, &model, caller, step_cap,
            );
            let report = cloud.run_with_toolkit(&handle, &mut brain, &toolkit);
            if let Some(rec) = &record {
                let responses = brain.caller().recorded();
                match save_record(rec, &workdir_s, &responses) {
                    Ok(()) => println!(
                        "\n  [record] saved {} model responses to {rec} (replay with --replay)",
                        responses.len()
                    ),
                    Err(e) => eprintln!("\n  [record] failed to save {rec}: {e}"),
                }
            }
            report
        };

        // Narrate the real transcript (every line traces to a receipt / refusal).
        let transcript = transcript_of(&report);
        for s in &transcript {
            let mark = if s.outcome == "admitted" {
                "✓"
            } else {
                "✗"
            };
            println!("  {mark} step {:>2}  {}", s.n, s.action);
            println!("           {}", s.outcome);
            if let Some(sum) = &s.tool_summary {
                for line in indent(sum, "           │ ").lines() {
                    println!("{line}");
                }
            }
        }
        if transcript.is_empty() {
            println!("  (the model committed no admitted action)");
        }
        println!();
        println!(
            "  → {} admitted · {} cap-refused · {} budget-refused · consumed {}¢ · headroom {}¢",
            report.admitted,
            report.cap_refused,
            report.budget_refused,
            report.consumed,
            report.headroom
        );
        println!();

        // SCALE: fork a sub-agent with a NARROWER bundle it provably cannot exceed.
        let subagent_run = if scale {
            Some(run_scale_demo(&cloud, &handle, &toolkit))
        } else {
            None
        };

        // Record the brain faithfully: for hermes-cli the model/endpoint are the
        // confined harness (no remote endpoint, auth lives inside the subprocess).
        let (rec_model, rec_endpoint) = match brain_kind {
            BrainKind::HermesCli => (
                "hermes (Nous Hermes CLI harness)".to_string(),
                "hermes-cli://local (subprocess; auth inside the harness)".to_string(),
            ),
            _ => (model, base),
        };
        // Brain provenance: the replay arm (a recorded brain) is only taken when NOT
        // hermes-cli AND a --replay record was supplied. Stamp it into the artifact so
        // `run.json` is honest standalone (the model/endpoint fields carry the live
        // defaults even under --replay).
        let brain_mode = if brain_kind != BrainKind::HermesCli && replay.is_some() {
            "replay"
        } else {
            "live"
        }
        .to_string();
        let live_run = LiveRun {
            goal,
            model: rec_model,
            endpoint: rec_endpoint,
            brain_mode,
            funding,
            budget_cents: budget,
            caps: handle.caps.clone(),
            workdir: workdir_s,
            transcript,
            run: report,
            subagent_run,
        };

        let json = serde_json::to_string_pretty(&live_run).expect("run serializes");
        if let Err(e) = std::fs::write(&out, json) {
            eprintln!("failed to write {out}: {e}");
            return ExitCode::FAILURE;
        }
        println!("  → wrote the receipt to {out}");
        println!("  → audit it yourself:  dregg-agent verify {out}\n");
        ExitCode::SUCCESS
    }

    // ── the SCALE / attenuation demo (deterministic, real tools) ──────────────

    fn run_scale_demo(
        cloud: &AgentCloud,
        parent: &dregg_agent::agent::AgentHandle,
        toolkit: &OperatorTools,
    ) -> dregg_agent::agent::AgentRunReport {
        println!("──[ SCALE ]── fork a sub-agent with a NARROWER cap bundle (no-amplify)\n");
        // The child keeps shell ONLY (drops http / spend / fs if the parent had them).
        let child_spec = AgentSpec::new("agent:operator/burst", parent.budget.min(50)).with_shell();
        let child = match cloud.deploy_subagent(parent, &child_spec) {
            Ok(c) => c,
            Err(e) => {
                println!("   (sub-agent not forked: {e})\n");
                // Return an empty, still-verifiable report by running an empty plan.
                return cloud.run_with_toolkit(parent, &mut PlannedBrain::new(vec![]), toolkit);
            }
        };
        println!(
            "   ✓ sub-agent deployed (shell only, budget {}¢) — provably narrower",
            child.budget
        );
        // One in-bundle op + two it CANNOT reach (no http grant, no pay grant —
        // a Stripe pay to a vendor outside the child's bundle is cap-refused).
        let plan = vec![
            AgentAction::Op(ToolCall::new(
                "shell",
                [("cmd".into(), "echo 'sub-agent at work'".into())],
            )),
            AgentAction::Op(ToolCall::new(
                "http_get",
                [("url".into(), "https://api.github.com/zen".into())],
            )),
            AgentAction::Op(ToolCall::new(
                op::STRIPE_PAY,
                [
                    ("vendor".into(), "openai".into()),
                    ("amount_cents".into(), "5".into()),
                    ("memo".into(), "burst".into()),
                ],
            )),
        ];
        let report = cloud.run_with_toolkit(&child, &mut PlannedBrain::new(plan), toolkit);
        for s in transcript_of(&report) {
            let mark = if s.outcome == "admitted" {
                "✓"
            } else {
                "✗"
            };
            println!("   {mark} {:<28} {}", s.action, s.outcome);
        }
        println!();
        report
    }

    // ── caps parsing ──────────────────────────────────────────────────────────

    struct Bundle {
        spec: AgentSpec,
        services: Vec<String>,
        op_tools: Vec<String>,
        cells: Vec<String>,
    }

    fn parse_caps(caps: &str, id: &str, budget: i64, workdir: &str) -> Result<Bundle, String> {
        let mut spec = AgentSpec::new(id, budget);
        let mut services = Vec::new();
        let mut op_tools = Vec::new();
        let mut cells = Vec::new();
        for tok in caps.split(',').map(str::trim).filter(|t| !t.is_empty()) {
            match tok {
                "shell" => {
                    spec = spec.with_shell();
                    op_tools.push(op::SHELL.to_string());
                }
                "fs" => {
                    spec = spec.with_workdir_fs(workdir);
                    for t in [op::FS_READ, op::FS_WRITE, op::LIST_DIR, op::MKDIR] {
                        op_tools.push(t.to_string());
                    }
                }
                // The Stripe Link skill (`stripe_pay`), per-vendor. `pay:VENDOR`
                // grants exactly that vendor; bare `spend` grants any vendor.
                t if t.starts_with("pay:") => {
                    let vendor = &t["pay:".len()..];
                    spec = spec.with_stripe_pay(vendor);
                    op_tools.push(op::STRIPE_PAY.to_string());
                }
                "spend" => {
                    spec =
                        spec.with_grant(dregg_agent::grant::CapGrant::Prefix("pay:".to_string()));
                    op_tools.push(op::STRIPE_PAY.to_string());
                }
                // The Stripe Projects skill (`stripe_provision`), per-provider.
                t if t.starts_with("provision:") => {
                    let provider = &t["provision:".len()..];
                    spec = spec.with_stripe_provision(provider);
                    op_tools.push(op::STRIPE_PROVISION.to_string());
                }
                t if t.starts_with("http:") => {
                    let host = &t["http:".len()..];
                    spec = spec.with_http_host(host);
                    op_tools.push(op::HTTP_GET.to_string());
                }
                t if t.starts_with("git:") => {
                    let host = &t["git:".len()..];
                    spec = spec.with_http_host(host);
                    op_tools.push(op::GIT_CLONE.to_string());
                }
                t if t.starts_with("cell:") => {
                    let path = &t["cell:".len()..];
                    spec = spec.with_cell(path);
                    cells.push(path.to_string());
                }
                // A bare token is a flat invoke service (e.g. run_tests).
                other => {
                    spec = spec.with_service(other);
                    services.push(other.to_string());
                }
            }
        }
        op_tools.sort();
        op_tools.dedup();
        Ok(Bundle {
            spec,
            services,
            op_tools,
            cells,
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn make_brain<C: OpenAICompatCaller>(
        goal: &str,
        services: &[String],
        cells: &[String],
        op_tools: &[String],
        key: ProviderKey,
        base: &str,
        model: &str,
        caller: C,
        step_cap: u64,
    ) -> OpenAICompatBrain<C> {
        OpenAICompatBrain::with_base(goal, services.to_vec(), cells.to_vec(), key, base, model, caller)
            .with_op_tools(op_tools.to_vec())
            .with_system_note("Work step by step using ONE tool call per turn. Keep reasoning brief. Call finish when the goal is met.")
            .with_step_cap(step_cap)
    }

    // ── real runners ───────────────────────────────────────────────────────────

    /// A real HTTP GET via reqwest blocking (bounded body), off any async runtime.
    pub fn real_http(url: &str) -> Result<HttpResp, String> {
        let url = url.to_string();
        let handle = std::thread::spawn(move || -> Result<HttpResp, String> {
            let client = reqwest::blocking::Client::builder()
                .timeout(Duration::from_secs(30))
                .user_agent("dregg-agent/0.1")
                .build()
                .map_err(|e| format!("client: {e}"))?;
            let resp = client.get(&url).send().map_err(|e| format!("get: {e}"))?;
            let status = resp.status().as_u16() as i64;
            let mut body = resp.text().map_err(|e| format!("body: {e}"))?;
            if body.len() > 4096 {
                body.truncate(4096);
            }
            Ok(HttpResp { status, body })
        });
        handle
            .join()
            .map_err(|_| "http thread panicked".to_string())?
    }

    // ── keys + record/replay ────────────────────────────────────────────────────

    fn nvidia_key() -> Option<ProviderKey> {
        ProviderKey::from_env("nvidia", "NVIDIA_API_KEY").or_else(|| {
            std::env::var_os("HOME")
                .map(|h| Path::new(&h).join(".nvidiakey"))
                .and_then(|p| ProviderKey::from_file("nvidia", p))
        })
    }

    /// The model key for a brain profile: the Nous Portal key for `--brain hermes`,
    /// the NVIDIA key otherwise. `--brain hermes-cli` needs none (the harness holds
    /// its own auth inside the subprocess) and never reaches this path.
    fn model_key(kind: BrainKind) -> Option<ProviderKey> {
        match kind {
            BrainKind::Hermes => hermes::nous_portal_key(),
            BrainKind::Nemotron | BrainKind::HermesCli => nvidia_key(),
        }
    }

    /// The "no key" help line for a brain profile.
    fn key_help(kind: BrainKind) -> &'static str {
        match kind {
            BrainKind::Hermes => {
                "no Nous Portal key: put it in ~/.nousportalkey or set NOUS_PORTAL_KEY \
                 (or use --replay <resp.json>)"
            }
            _ => {
                "no model key: put it in ~/.nvidiakey or set NVIDIA_API_KEY \
                 (or use --replay <resp.json>)"
            }
        }
    }

    // ── (b) the real `hermes` CLI as the confined harness ───────────────────────

    /// Drive the **real `hermes` CLI** (or a configured ndjson wrapper) as the
    /// confined harness: it reasons with its own installed skills while dregg
    /// intercepts every skill-call through the cap-gate + budget + receipt. Live
    /// when the CLI / a tool-bridge is present; otherwise a faithful recorded demo.
    fn run_hermes_cli(
        cloud: &AgentCloud,
        handle: &AgentHandle,
        goal: &str,
        toolkit: &OperatorTools,
        step_cap: u64,
    ) -> AgentRunReport {
        match hermes::spawn_hermes_harness(goal) {
            Some(Ok(h)) => {
                println!(
                    "  [mode] LIVE — the `hermes` CLI is the brain; dregg intercepts every \
                     skill-call (cap-gate · budget · receipt)\n"
                );
                let mut brain = HarnessBrain::new(h).with_step_cap(step_cap);
                let report = cloud.run_with_toolkit(handle, &mut brain, toolkit);
                let _ = brain; // the brain owns the child; dropped here.
                report
            }
            Some(Err(e)) => {
                println!(
                    "  [mode] could not spawn the hermes harness ({e}); falling back to the \
                     recorded demo\n"
                );
                run_recorded_hermes(cloud, handle, toolkit, step_cap)
            }
            None => {
                println!(
                    "  [mode] RECORDED — the `hermes` CLI / a tool-bridge is not present; \
                     replaying hermes-shaped skill calls so the confinement teeth are visible. \
                     Set {} to a hermes wrapper that speaks the ndjson tool protocol for a live \
                     run.\n",
                    hermes::HERMES_CMD_ENV
                );
                run_recorded_hermes(cloud, handle, toolkit, step_cap)
            }
        }
    }

    /// The offline recorded confined-harness run: hermes-shaped skill calls through
    /// the same cap · budget · receipt rail (honestly labelled, never a faked live).
    fn run_recorded_hermes(
        cloud: &AgentCloud,
        handle: &AgentHandle,
        toolkit: &OperatorTools,
        step_cap: u64,
    ) -> AgentRunReport {
        let calls = hermes::recorded_hermes_demo_calls();
        let mut brain = HarnessBrain::new(MockHarness::new(calls)).with_step_cap(step_cap);
        cloud.run_with_toolkit(handle, &mut brain, toolkit)
    }

    /// The capture format: the recorded model responses plus the workdir they ran
    /// against (so a replay reuses it and the recorded tool calls resolve).
    #[derive(serde::Serialize, serde::Deserialize)]
    struct Record {
        workdir: String,
        responses: Vec<Value>,
    }

    fn save_record(path: &str, workdir: &str, responses: &[Value]) -> Result<(), String> {
        let rec = Record {
            workdir: workdir.to_string(),
            responses: responses.to_vec(),
        };
        let json = serde_json::to_string_pretty(&rec).map_err(|e| e.to_string())?;
        std::fs::write(path, json).map_err(|e| e.to_string())
    }

    fn load_record(path: &str) -> Result<Record, String> {
        let raw = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
        // Accept either the {workdir, responses} record or a bare responses array.
        if let Ok(rec) = serde_json::from_str::<Record>(&raw) {
            return Ok(rec);
        }
        let responses: Vec<Value> = serde_json::from_str(&raw).map_err(|e| e.to_string())?;
        Ok(Record {
            workdir: String::new(),
            responses,
        })
    }

    fn indent(s: &str, prefix: &str) -> String {
        s.lines()
            .map(|l| format!("{prefix}{l}"))
            .collect::<Vec<_>>()
            .join("\n")
    }

    /// A recording wrapper around the live caller: tees every provider response so
    /// a good real run can be saved (`--record`) and later replayed (`--replay`).
    /// The key still rides ONLY in the inner caller's auth header.
    pub struct TeeCaller<C: OpenAICompatCaller> {
        inner: C,
        recorded: std::cell::RefCell<Vec<Value>>,
    }

    impl<C: OpenAICompatCaller> TeeCaller<C> {
        pub fn new(inner: C) -> TeeCaller<C> {
            TeeCaller {
                inner,
                recorded: std::cell::RefCell::new(Vec::new()),
            }
        }
        pub fn recorded(&self) -> Vec<Value> {
            self.recorded.borrow().clone()
        }
    }

    impl<C: OpenAICompatCaller> OpenAICompatCaller for TeeCaller<C> {
        fn complete(
            &mut self,
            endpoint: &str,
            api_key: &str,
            request: &Value,
        ) -> Result<Value, String> {
            let resp = self.inner.complete(endpoint, api_key, request)?;
            self.recorded.borrow_mut().push(resp.clone());
            Ok(resp)
        }
    }
}

// ─────────────────────────────── session / attach (the hosted REPL) ──────────
//
// The interactive twin of `run`: a persistent, budget-bounded, cap-gated agent
// session the user DRIVES goal by goal. `session` runs it locally; `attach` is
// the same REPL scoped to one account — the target an SSH `authorized_keys`
// `command="dregg-agent attach --account … --budget … --caps …"` drops a
// connecting user into (so the SSH session IS the agent REPL, per-user-isolated,
// the brain + tools server-side). Std-only on the recorded path (`--replay`);
// the live model path is behind `live-brain`, exactly like `run`.

mod repl {
    use std::io::{BufRead, Write};
    use std::path::PathBuf;
    use std::process::ExitCode;
    use std::time::Duration;

    use dregg_agent::agent::AgentBrain;
    use dregg_agent::brain::{OpenAICompatBrain, ProviderKey, RecordedOpenAICaller};
    use dregg_agent::session::{CapBundle, Confinement, Session, parse_caps_confined};
    use dregg_agent::session_store::ConsumedStore;
    use dregg_agent::toolkit::Toolkit;
    use dregg_agent::tools::OperatorTools;
    use serde_json::Value;

    use super::{flag, has, rule};

    /// `session` (local) vs `attach` (the SSH forced-command drop-in for one account).
    #[derive(Clone, Copy, PartialEq, Eq)]
    pub enum Mode {
        Session,
        Attach,
    }

    /// The default bundle for a LOCAL interactive session (the user's own box): a
    /// real shell + workdir fs + GitHub egress (a useful, bounded starter powerbox).
    const LOCAL_DEFAULT_CAPS: &str = "shell,fs,http:api.github.com";

    /// The default bundle for a HOSTED session (`attach`, or `session --hosted`):
    /// the **lexically-confined** tools only — NO raw `shell`. A hosted box also
    /// holds the operator's keys, and a raw shell can read them (`cat
    /// /home/op/.stripekey`) past the in-process env-scrub, so the hosted default is
    /// fs (workdir-rooted) + per-host GitHub egress. `shell` returns on a hosted box
    /// only behind per-tenant OS isolation (see DreggNet/docs/HOSTED-ISOLATION.md).
    const HOSTED_DEFAULT_CAPS: &str = "fs,http:api.github.com";

    const STEER: &str = "Work step by step using ONE tool call per turn. Keep reasoning brief. Call finish \
         when the goal is met.";

    /// Where the brain comes from for THIS session (one source, a fresh brain per goal).
    enum BrainSource {
        /// A recorded transport (std-only): canned model responses, replayed (and
        /// repeated) so the confinement teeth + the loop are demoable without a key.
        Replay {
            responses: Vec<Value>,
            base: String,
            model: String,
        },
        /// The live model path (BYO key), behind `live-brain`.
        #[cfg(feature = "live-brain")]
        Live {
            key: ProviderKey,
            base: String,
            model: String,
        },
    }

    impl BrainSource {
        /// The `(model, endpoint)` pair recorded into the session artifact.
        fn model_endpoint(&self) -> (String, String) {
            match self {
                BrainSource::Replay { base, model, .. } => (model.clone(), base.clone()),
                #[cfg(feature = "live-brain")]
                BrainSource::Live { base, model, .. } => (model.clone(), base.clone()),
            }
        }
        /// A one-line mode label for the banner.
        fn label(&self) -> String {
            match self {
                BrainSource::Replay { .. } => {
                    "recorded (replayed model responses — the confinement teeth are live)".into()
                }
                #[cfg(feature = "live-brain")]
                BrainSource::Live { model, base, .. } => format!("live model {model} @ {base}"),
            }
        }
        /// The brain provenance stamped into `LiveRun.brain_mode` — `"replay"` for a
        /// recorded transport, `"live"` for the BYO-key model path — so the session
        /// artifact is honest standalone about whether the model was actually called.
        fn brain_mode(&self) -> String {
            match self {
                BrainSource::Replay { .. } => "replay".into(),
                #[cfg(feature = "live-brain")]
                BrainSource::Live { .. } => "live".into(),
            }
        }
    }

    /// `dregg-agent session` / `dregg-agent attach`.
    pub fn cmd_session(args: &[String], mode: Mode) -> ExitCode {
        let account = flag(args, "--account")
            .unwrap_or(if mode == Mode::Attach {
                // attach without an explicit account is a misconfiguration — the
                // forced-command must scope to one. Default to a clearly-local id.
                "dga1_attached"
            } else {
                "dga1_local"
            })
            .to_string();
        let budget: i64 = flag(args, "--budget")
            .and_then(|s| s.parse().ok())
            .unwrap_or(500);

        // `--os-isolation` is REFUSED (fail-closed). It used to flip a hosted session
        // back to the local posture — re-granting a raw `shell` on the operator-key-
        // holding host — on the mere ASSERTION that a per-tenant OS jail was present.
        // But the jail (`dreggnet-agent-host`'s `JailSpec`/`bwrap`) is not wired into
        // any run path: setting the flag never actually confined anything, so it was a
        // security mechanism presented as enforced that ran nowhere. Until the jail is
        // genuinely wired (the attach process re-execs inside `bwrap`), a hosted shell
        // must be REFUSED, never handed out behind a decorative flag. So the flag hard-
        // errors rather than silently restoring the dangerous capability.
        if has(args, "--os-isolation") {
            eprintln!(
                "--os-isolation is not available: per-tenant OS isolation (the bwrap jail) is \
                 not wired into the run path, so it cannot safely restore a raw shell on the \
                 key-holding host. A hosted session stays shell-disabled (the safe default). \
                 Run locally for a raw shell. See DreggNet/docs/HOSTED-ISOLATION.md."
            );
            return ExitCode::FAILURE;
        }
        // The confinement posture. `attach` is the hosted SSH/portal drop-in and is
        // ALWAYS hosted (it runs on shared infra that holds the operator's keys);
        // `session` is local by default but `--hosted`/`--untrusted` forces the
        // hosted posture (no raw shell — a raw shell can read the operator's keys).
        let forced_hosted =
            mode == Mode::Attach || has(args, "--hosted") || has(args, "--untrusted");
        let confinement = if forced_hosted {
            Confinement::Hosted
        } else {
            Confinement::Local
        };
        let default_caps = if confinement == Confinement::Hosted {
            HOSTED_DEFAULT_CAPS
        } else {
            LOCAL_DEFAULT_CAPS
        };
        let caps_str = flag(args, "--caps").unwrap_or(default_caps).to_string();
        let step_cap: u64 = flag(args, "--step-cap")
            .and_then(|s| s.parse().ok())
            .unwrap_or(16);
        let out = flag(args, "--out").map(String::from);

        let workdir = flag(args, "--workdir")
            .map(PathBuf::from)
            .unwrap_or_else(|| {
                std::env::temp_dir().join(format!(
                    "dregg-agent-session-{}-{}",
                    account.replace(['/', ':'], "_"),
                    std::process::id()
                ))
            });
        if let Err(e) = std::fs::create_dir_all(&workdir) {
            eprintln!("cannot create workdir {}: {e}", workdir.display());
            return ExitCode::FAILURE;
        }
        let workdir = workdir.canonicalize().unwrap_or(workdir);
        let workdir_s = workdir.to_string_lossy().to_string();

        let bundle = match parse_caps_confined(
            &caps_str,
            "agent:session",
            budget,
            &workdir_s,
            confinement,
        ) {
            Ok(b) => b,
            Err(e) => {
                eprintln!("bad --caps: {e}");
                return ExitCode::FAILURE;
            }
        };
        let mut spec = bundle.spec.clone();
        spec.asset = "USD-CENTS".into();

        // The durable per-account store (keyed by account id under a stable state dir,
        // $DREGG_AGENT_STATE_DIR or ~/.dregg-agent/state) holds two things that must
        // span SSH detach/re-attach: the cumulative spend (so the ceiling is not reset
        // by reconnecting) AND the receipt-chain secret (so a resumed session re-signs
        // with the SAME key — the renter's pinned `(signer, tip)` keeps verifying).
        let store = ConsumedStore::open_default();

        // Recover (or first-mint + persist) the account's RANDOM receipt-chain secret
        // and open the session under it. This replaces the old public
        // `BLAKE3(agent_id)` seed: the agent id is printed in cleartext in every
        // report, so a hashed-id seed let any report-holder re-derive the signing key
        // and forge the chain. A persisted random secret closes that third-party hole.
        let receipt_secret = match store.ensure_receipt_secret(&account, spec.budget) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("could not load/create the receipt-chain secret for {account}: {e}");
                return ExitCode::FAILURE;
            }
        };
        let mut sess = match Session::open_with_secret(&account, spec, receipt_secret) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("session open failed: {e}");
                return ExitCode::FAILURE;
            }
        };

        // Restore the account's PERSISTED cumulative spend so the budget ceiling
        // spans SSH detach/re-attach. Each attach process opens a fresh in-memory
        // meter; without this the ceiling would silently reset to full on every
        // reconnect (an unbounded-spend hole).
        let prior_consumed = store.load_consumed(&account);
        sess.restore_consumed(prior_consumed);

        let brain_src = match build_brain_source(args) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("{e}");
                return ExitCode::FAILURE;
            }
        };

        // The server-side toolkit: a real shell (workdir-confined, timeout-bounded)
        // + workdir fs + the real Stripe Skills (recorded offline). http egress is
        // wired on the live build (the same runner `run` uses).
        let timeout = Duration::from_secs(60);
        #[allow(unused_mut)]
        let mut toolkit = OperatorTools::new(Toolkit::new(), &workdir)
            .with_shell(move |cmd, cwd| dregg_agent::tools::real_shell(cmd, cwd, timeout))
            .with_stripe_skills_boxed(dregg_agent::stripe_skills::detect());
        #[cfg(feature = "live-brain")]
        {
            toolkit = toolkit.with_http(super::live::real_http);
        }

        banner(mode, &sess, &workdir_s, &brain_src);
        match confinement {
            Confinement::Hosted => println!(
                "  CONFINE hosted — lexically-confined tools only (no raw shell; the host holds \
                 operator keys). Run locally for a raw shell."
            ),
            Confinement::Local => println!(
                "  CONFINE local — full toolkit incl. raw shell (this is your own machine)."
            ),
        }

        // ATTACH one-shot: `ssh acct@host "do the thing"` arrives as
        // SSH_ORIGINAL_COMMAND — run that single goal non-interactively and exit.
        if mode == Mode::Attach {
            if let Some(cmd) = std::env::var("SSH_ORIGINAL_COMMAND")
                .ok()
                .filter(|c| !c.trim().is_empty())
            {
                run_one_goal(
                    &mut sess,
                    cmd.trim(),
                    &bundle,
                    &brain_src,
                    step_cap,
                    &toolkit,
                );
                persist_consumed(&store, &account, &sess);
                finish(&sess, &brain_src, &workdir_s, &out);
                return ExitCode::SUCCESS;
            }
        }

        // The interactive REPL: a goal per line; `:`-commands inspect the session.
        let stdin = std::io::stdin();
        let mut lines = stdin.lock().lines();
        loop {
            prompt(&sess);
            let line = match lines.next() {
                Some(Ok(l)) => l,
                _ => break, // EOF / detach
            };
            let g = line.trim();
            if g.is_empty() {
                continue;
            }
            match g {
                ":quit" | ":exit" | ":q" => break,
                ":help" | ":h" => print_help(),
                ":status" | ":budget" => print_status(&sess),
                ":caps" => print_caps(&sess),
                ":history" => print_history(&sess),
                ":verify" => print_verify(&sess),
                other if other.starts_with(':') => {
                    println!("  unknown command `{other}` — try :help")
                }
                _ => {
                    run_one_goal(&mut sess, g, &bundle, &brain_src, step_cap, &toolkit);
                    // Persist the drawdown after EVERY goal so a detach at any point
                    // (incl. an abrupt SSH drop) leaves the ceiling correct for the
                    // next attach — the budget can never be reset by reconnecting.
                    persist_consumed(&store, &account, &sess);
                    if sess.exhausted() {
                        println!(
                            "  [budget exhausted — the session ceiling is fully drawn; further \
                             priced actions are refused in-band]"
                        );
                    }
                }
            }
        }
        persist_consumed(&store, &account, &sess);
        finish(&sess, &brain_src, &workdir_s, &out);
        ExitCode::SUCCESS
    }

    /// Persist the session's cumulative consumed to the durable per-account store so
    /// the budget ceiling spans SSH detach/re-attach. Best-effort: a write failure is
    /// logged (fail-loud) but does not abort the session — the in-band meter still
    /// bounds THIS process; the risk a failed write carries is only the reset-on-
    /// reconnect hole, which the operator sees on stderr.
    fn persist_consumed(store: &ConsumedStore, account: &str, sess: &Session) {
        if let Err(e) = store.save_consumed(account, sess.consumed(), sess.budget()) {
            eprintln!(
                "warning: could not persist the session budget for {account}: {e} — the spend \
                 ceiling may not hold across re-attach"
            );
        }
    }

    /// Pick the brain source from the args: `--replay` → recorded (std-only);
    /// otherwise the live model (behind `live-brain`), else a helpful error.
    fn build_brain_source(args: &[String]) -> Result<BrainSource, String> {
        let base = flag(args, "--base")
            .or_else(|| flag(args, "--llm-base"))
            .unwrap_or("https://integrate.api.nvidia.com/v1")
            .to_string();
        let model = flag(args, "--model")
            .or_else(|| flag(args, "--llm-model"))
            .unwrap_or("recorded")
            .to_string();
        if let Some(path) = flag(args, "--replay") {
            let responses = load_responses(path)?;
            return Ok(BrainSource::Replay {
                responses,
                base,
                model,
            });
        }
        #[cfg(feature = "live-brain")]
        {
            let key = ProviderKey::from_env("nvidia", "NVIDIA_API_KEY")
                .or_else(|| {
                    std::env::var_os("HOME")
                        .map(|h| std::path::Path::new(&h).join(".nvidiakey"))
                        .and_then(|p| ProviderKey::from_file("nvidia", p))
                })
                .ok_or_else(|| {
                    "no model key: put it in ~/.nvidiakey or set NVIDIA_API_KEY (or use \
                     --replay <resp.json>)"
                        .to_string()
                })?;
            let model = if model == "recorded" {
                "nvidia/llama-3.3-nemotron-super-49b-v1".to_string()
            } else {
                model
            };
            return Ok(BrainSource::Live { key, base, model });
        }
        #[cfg(not(feature = "live-brain"))]
        Err(
            "a session needs a brain: pass --replay <resp.json> for the recorded transport, \
             or rebuild with --features live-brain for a live model"
                .to_string(),
        )
    }

    /// A fresh brain for ONE goal (the REPL hands each goal its own conversation).
    fn make_brain(
        src: &BrainSource,
        goal: &str,
        bundle: &CapBundle,
        step_cap: u64,
    ) -> Box<dyn AgentBrain> {
        match src {
            BrainSource::Replay {
                responses,
                base,
                model,
            } => {
                let caller = RecordedOpenAICaller::repeating(responses.clone());
                Box::new(
                    OpenAICompatBrain::with_base(
                        goal,
                        bundle.services.clone(),
                        bundle.cells.clone(),
                        ProviderKey::unauthenticated(),
                        base,
                        model.clone(),
                        caller,
                    )
                    .with_op_tools(bundle.op_tools.clone())
                    .with_system_note(STEER)
                    .with_step_cap(step_cap),
                )
            }
            #[cfg(feature = "live-brain")]
            BrainSource::Live { key, base, model } => {
                let caller = dregg_agent::brain::LiveOpenAICompatCaller::new();
                Box::new(
                    OpenAICompatBrain::with_base(
                        goal,
                        bundle.services.clone(),
                        bundle.cells.clone(),
                        key.clone(),
                        base,
                        model.clone(),
                        caller,
                    )
                    .with_op_tools(bundle.op_tools.clone())
                    .with_system_note(STEER)
                    .with_step_cap(step_cap),
                )
            }
        }
    }

    /// Run one typed goal through the session and narrate its delta.
    fn run_one_goal(
        sess: &mut Session,
        goal: &str,
        bundle: &CapBundle,
        src: &BrainSource,
        step_cap: u64,
        toolkit: &OperatorTools,
    ) {
        println!("\n──[ goal ]── {goal}");
        println!("──[ reason → act → observe ]── (cap-gated · metered · receipted)\n");
        let mut brain = make_brain(src, goal, bundle, step_cap);
        let gr = sess.run_goal(goal, brain.as_mut(), toolkit);
        for s in &gr.steps {
            let mark = if s.outcome == "admitted" {
                "✓"
            } else {
                "✗"
            };
            println!("  {mark} step {:>2}  {}", s.n, s.action);
            println!("           {}", s.outcome);
            if let Some(sum) = &s.tool_summary {
                for line in sum.lines() {
                    println!("           │ {line}");
                }
            }
        }
        if gr.steps.is_empty() {
            println!("  (the model committed no admitted action)");
        }
        println!(
            "\n  → {} admitted · {} cap-refused · {} budget-refused · consumed {}¢ / {}¢ · headroom {}¢",
            gr.admitted,
            gr.cap_refused,
            gr.budget_refused,
            gr.consumed,
            sess.budget(),
            gr.headroom
        );
    }

    fn banner(mode: Mode, sess: &Session, workdir: &str, src: &BrainSource) {
        rule();
        match mode {
            Mode::Session => {
                println!(
                    "  dregg-agent — a hosted, verifiable agent SESSION (drive it goal by goal)"
                )
            }
            Mode::Attach => println!(
                "  dregg-agent — you are ATTACHED to your hosted, verifiable agent session"
            ),
        }
        rule();
        println!();
        println!("  ACCOUNT {}", sess.account());
        println!("  BRAIN   {}", src.label());
        println!(
            "  BUDGET  {}¢   CAPS  {}",
            sess.budget(),
            sess.caps().join("  ·  ")
        );
        println!("  WORKDIR {workdir}");
        println!("  AGENT   {}", sess.agent_id());
        println!();
        println!(
            "  Type a goal and press enter. Commands: :status  :caps  :verify  :history  :help  :quit"
        );
    }

    fn prompt(sess: &Session) {
        print!("\n[{} · {}¢ left] goal> ", sess.account(), sess.headroom());
        let _ = std::io::stdout().flush();
    }

    fn print_help() {
        println!(
            "  commands:\n\
             \x20   <goal>     run a goal (reason→act→observe, cap-gated · metered · receipted)\n\
             \x20   :status    the running budget (consumed / ceiling / headroom)\n\
             \x20   :caps      the cap bundle this session is scoped to\n\
             \x20   :verify    re-witness the WHOLE session so far (host-untrusted)\n\
             \x20   :history   the goals run so far\n\
             \x20   :quit      detach (the session artifact can still be verified)"
        );
    }

    fn print_status(sess: &Session) {
        println!(
            "  budget {}¢ · consumed {}¢ · headroom {}¢ · {} goal(s) · {} receipted action(s)",
            sess.budget(),
            sess.consumed(),
            sess.headroom(),
            sess.goal_count(),
            sess.report().receipts.len()
        );
    }

    fn print_caps(sess: &Session) {
        println!("  cap bundle (a sub-agent can only narrow these):");
        for c in sess.caps() {
            println!("   · {c}");
        }
    }

    fn print_history(sess: &Session) {
        if sess.history().is_empty() {
            println!("  (no goals yet)");
            return;
        }
        for (i, g) in sess.history().iter().enumerate() {
            println!(
                "  {:>2}. {}  ({} admitted · {} cap-refused · {} budget-refused · {}¢)",
                i + 1,
                g.goal,
                g.admitted,
                g.cap_refused,
                g.budget_refused,
                g.consumed
            );
        }
    }

    fn print_verify(sess: &Session) {
        match sess.verify() {
            Ok(v) => println!(
                "  ✓ the WHOLE session re-witnesses: {} signed action(s) in one chain, \
                 consumed {}¢ ≤ ceiling {}¢ (headroom {}¢) — host untrusted",
                v.actions, v.consumed, v.budget, v.headroom
            ),
            Err(e) => println!("  ✗ session does NOT verify: {e}"),
        }
    }

    /// On detach: print the final verify and (optionally) write the session
    /// artifact, which `dregg-agent verify <file>` re-witnesses offline.
    fn finish(sess: &Session, src: &BrainSource, workdir: &str, out: &Option<String>) {
        println!();
        rule();
        print_verify(sess);
        if let Some(path) = out {
            let report = sess.report();
            let (model, endpoint) = src.model_endpoint();
            let brain_mode = src.brain_mode();
            let goals: Vec<String> = sess.history().iter().map(|g| g.goal.clone()).collect();
            let live = dregg_agent::live::LiveRun {
                goal: if goals.is_empty() {
                    "(empty session)".into()
                } else {
                    goals.join(" ; ")
                },
                model,
                endpoint,
                brain_mode,
                funding: format!(
                    "hosted session budget of {}¢ (the ceiling the whole session draws from)",
                    sess.budget()
                ),
                budget_cents: sess.budget(),
                caps: sess.caps().to_vec(),
                workdir: workdir.to_string(),
                transcript: dregg_agent::live::transcript_of(&report),
                run: report,
                subagent_run: None,
            };
            match serde_json::to_string_pretty(&live) {
                Ok(json) => match std::fs::write(path, json) {
                    Ok(()) => {
                        println!("  → wrote the session receipt to {path}");
                        println!("  → audit it yourself:  dregg-agent verify {path}");
                    }
                    Err(e) => eprintln!("  failed to write {path}: {e}"),
                },
                Err(e) => eprintln!("  failed to serialize session: {e}"),
            }
        }
        rule();
    }

    /// Load recorded model responses: a bare JSON array of chat-completions
    /// responses, or a `{ "responses": [...] }` object (the `--record` capture).
    fn load_responses(path: &str) -> Result<Vec<Value>, String> {
        let raw = std::fs::read_to_string(path).map_err(|e| format!("cannot read {path}: {e}"))?;
        if let Ok(v) = serde_json::from_str::<Vec<Value>>(&raw) {
            return Ok(v);
        }
        let obj: Value =
            serde_json::from_str(&raw).map_err(|e| format!("cannot parse {path}: {e}"))?;
        obj.get("responses")
            .and_then(|r| r.as_array())
            .map(|a| a.to_vec())
            .ok_or_else(|| format!("{path}: expected a JSON array or a {{responses:[…]}} object"))
    }
}
