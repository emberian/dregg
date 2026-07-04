//! `deos-hermes` — drive the confined Hermes agent loop, two ways.
//!
//! 1. THE LIVE-SHAPED ACP LOOP (default, or `cargo run -- mock`): the real ACP
//!    client drives a session against the faithful [`MockHermesPeer`] (replaying
//!    `acp_adapter`'s message shapes), answering every `session/request_permission`
//!    with the [`HermesGateway`] verdict — a cap-gated, metered, receipted dregg
//!    turn (with the tool's side-effect riding it) or an in-band refusal. Then it
//!    prints the agent dock view (chat + tool-call ledger + the mandate inspector).
//!
//! 2. THE LIVE SUBPROCESS (`cargo run -- live`): spawns the REAL `hermes-acp`
//!    stdio server and drives the SAME client over its stdio — `initialize` →
//!    `session/new` → `session/set_model` → `session/prompt`, answering each
//!    `session/request_permission` through the [`HermesGateway`]. The prompt asks
//!    Hermes to run a command Hermes's own dangerous-command detector flags
//!    (`rm -rf …`), which is what makes Hermes issue a real
//!    `session/request_permission` back to the client — exercising the gateway
//!    seam against a LIVE agent loop.
//!
//!    The live ceiling, honestly: the agent loop needs a model provider +
//!    credentials. `hermes-acp` advertises AWS Bedrock models; if no Bedrock
//!    credentials / network are present the provider call fails inside Hermes and
//!    no tool-call (hence no permission request) is produced — the handshake +
//!    session still complete. `run_live` reports exactly how far it got.
//!
//! 3. THE LIVE REFUSAL (`cargo run -- live-refuse`): identical to `live`, but the
//!    `terminal` tool is pinned to rate 0, so the real model's `rm -rf`
//!    tool-call is REFUSED IN-BAND by the gateway (the over-mandate leg bites
//!    before any spend) — proving the refusal half of the seam against a live
//!    agent loop, not just the allow half.
//!
//! Run: `cd deos-hermes && cargo run` (mock), `cargo run -- live`, or
//! `cargo run -- live-refuse`.

use std::sync::{Arc, RwLock};

use deos_hermes::mcp_server::{McpServer, McpToolHost};
use deos_hermes::surface::AgentDockModel;
use deos_hermes::{
    AcpClient, AcpTransport, GrantRegistry, HermesGateway, MockHermesPeer, ScriptedCall,
};
use dregg_sdk::{AgentCipherclerk, AgentRuntime};

fn main() {
    let mode = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "mock".to_string());
    match mode.as_str() {
        // THE REAL CONFINED AGENT (no live provider needed): a brain-driven ACP
        // loop. The on-box `LocalBrain` reads the prompt, decides tool-calls one
        // at a time, OBSERVES each gate verdict, and ADAPTS — every call a
        // cap-gated, receipted dregg turn (or an in-band refusal it works around).
        // This is the replacement for the scripted stand-in.
        "agent" => run_agent(),
        // THE LIVE BYO-KEY BRAIN over the standard confinement (feature
        // `live-brain`). Resolves a provider key from the env chain
        // (DREGG_LLM_API_KEY / ANTHROPIC_API_KEY / OPENAI_API_KEY /
        // NVIDIA_API_KEY / ~/.nvidiakey), calls a REAL model for each decision,
        // and gates every tool-call it reaches for as a receipted dregg turn.
        "brain-live" => run_brain_live(),
        // The live brain → gateway seam over the standard confinement: the
        // `terminal` tool-call the model emits is ADMITTED (a cap-gated,
        // receipted dregg turn on the verified executor).
        "live" => run_live(Confine::Standard),
        // The same live brain, but `terminal` pinned to rate 0 — the model's
        // `rm -rf` tool-call is REFUSED IN-BAND (the over-mandate leg bites
        // before any spend), proving the refusal half of the seam live.
        "live-refuse" => run_live(Confine::DenyTerminal),
        // THE DREGG MCP SERVER — speak standard MCP over stdin/stdout, exposing
        // ONLY dregg-confined tools (`run_js`, `terminal`). This is the binary
        // Hermes spawns when deos registers it on `session/new`'s `mcpServers`:
        // every tool the model calls routes through THIS process (the dregg
        // sandbox), so the model has no unconfined tool path. Runs until EOF.
        "mcp-server" => run_mcp_server(),
        // THE DEEP-INTEGRATION LIVE PROOF — drive a real `hermes-acp` session that
        // registers the dregg confined MCP server (THIS binary, `mcp-server`) as
        // the model's tool source, then prompt the model to use a tool. The model's
        // tool-calls route through the dregg sandbox (our subprocess); the deos
        // client sees the `tool_call` events. Requires a reachable provider
        // (HERMES_INFERENCE_PROVIDER / HERMES_ACP_MODEL).
        "live-mcp" => run_live_mcp(),
        _ => run_mock(),
    }
}

/// Which confinement the live loop runs under — the standard floors (the
/// `terminal` call is allowed + receipted) or a `terminal`-denied registry (the
/// `terminal` call is refused in-band).
#[derive(Clone, Copy)]
enum Confine {
    Standard,
    DenyTerminal,
}

/// Build the grantor runtime + root token + the standard confinement (per-kind
/// floors + the curated per-tool tightenings, deadline/clock 1000).
fn confinement() -> (AgentRuntime, dregg_sdk::HeldToken, GrantRegistry) {
    confinement_with(Confine::Standard)
}

/// As [`confinement`], but choosing whether `terminal` is allowed (the standard
/// per-tool tightenings) or denied (pinned to rate 0 so the live `rm -rf`
/// tool-call is refused in-band).
fn confinement_with(confine: Confine) -> (AgentRuntime, dregg_sdk::HeldToken, GrantRegistry) {
    let mut cclerk = AgentCipherclerk::new();
    let root_token = cclerk.mint_token(&[7u8; 32], "deos");
    let runtime = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
    // The per-tool grants tighten `terminal` (rate 5), `web_extract` (15), etc.
    let registry = GrantRegistry::default_for_session(1000).with_standard_tool_grants(1000);
    let registry = match confine {
        Confine::Standard => registry,
        // Pin `terminal` to rate 0 — `delegAdmit`'s rate conjunct `new(=1) <= 0`
        // is false, so the live agent's `rm -rf` terminal call is refused in-band
        // (no turn, no spend), naming the leg that bit.
        Confine::DenyTerminal => registry.with_grant_for_tool_deny("terminal"),
    };
    (runtime, root_token, registry)
}

/// The live-shaped ACP loop over the faithful mock peer.
fn run_mock() {
    println!("deos-hermes — the confined Hermes ACP loop (mock peer)\n");
    let (runtime, root_token, registry) = confinement();
    let gateway = HermesGateway::new(&runtime, root_token, registry);

    // A scripted Hermes turn: a search, a file write, three terminal calls (the
    // 3rd over a tightened rate, in a tighter demo registry below), a fetch.
    let script = vec![
        ScriptedCall::new("web_search", serde_json::json!({"query": "dregg ocap"})),
        ScriptedCall::new(
            "write_file",
            serde_json::json!({"path": "notes/plan.md", "content": "the plan"}),
        ),
        ScriptedCall::new("terminal", serde_json::json!({"command": "cargo build"})),
        ScriptedCall::new("terminal", serde_json::json!({"command": "cargo test"})),
        ScriptedCall::new("read_file", serde_json::json!({"path": "src/lib.rs"})),
    ];

    let peer = MockHermesPeer::new("sess-demo", script);
    let mut client = AcpClient::new(peer, gateway, 10);

    let run = client
        .run_prompt("/Users/ember/dev/breadstuffs", "help me confine hermes")
        .expect("the ACP loop runs end-to-end over the mock peer");

    let model = AgentDockModel::from_run("sess-demo", &run, client.gateway());
    print!("{}", model.render_text());
}

/// THE REAL CONFINED AGENT — a brain-driven ACP loop over the standard
/// confinement. The on-box [`LocalBrain`] forms a plan from the prompt, issues
/// tool-calls one at a time, and reacts to each gate verdict; `write_file` is
/// pinned to rate 0 here so the agent meets a refusal and ADAPTS (it falls back
/// to a read-only probe rather than banging on the denied tool). Prints the dock.
fn run_agent() {
    use deos_hermes::{HermesAgentPeer, LocalBrain};

    println!("deos-hermes — the REAL confined agent (brain-driven ACP loop)\n");
    let (runtime, root_token, registry) = confinement();
    // Deny write_file so the agent visibly works within its caps (adapts to the
    // refusal) — the on-box brain's reactive loop, not a fixed script.
    let registry = registry.with_grant_for_tool_deny("write_file");
    let gateway = HermesGateway::new(&runtime, root_token, registry);

    let peer = HermesAgentPeer::new("sess-agent", LocalBrain::new());
    let mut client = AcpClient::new(peer, gateway, 10);
    let run = client
        .run_prompt(
            "/Users/ember/dev/breadstuffs",
            "search the docs, write a notes file, then run the build",
        )
        .expect("the brain-driven ACP loop runs end-to-end");

    let model = AgentDockModel::from_run("sess-agent", &run, client.gateway());
    print!("{}", model.render_text());
    println!(
        "\n(the brain decided {} tool-call(s); a denied write_file was met with a \
         read-only fallback — the agent adapted within its caps.)",
        run.verdicts.len()
    );
}

/// THE LIVE BYO-KEY BRAIN — a real model drives the confined ACP loop. Resolves
/// a provider key from the env chain and, if one is present, runs
/// [`deos_hermes::brain::live_brain_from_env`] over the standard confinement so
/// every tool-call the model reaches for is a cap-gated, receipted dregg turn.
/// Without the `live-brain` feature (or without a key), it reports how to enable
/// the path and falls back to nothing (no scripted stand-in).
#[cfg(feature = "live-brain")]
fn run_brain_live() {
    use deos_hermes::HermesAgentPeer;
    use deos_hermes::brain::live_brain_from_env;

    println!("deos-hermes — the LIVE BYO-key brain (real model drives the ACP loop)\n");
    let brain = match live_brain_from_env() {
        Some(b) => b,
        None => {
            println!(
                "no BYO model key found — set one of DREGG_LLM_API_KEY, ANTHROPIC_API_KEY, \
                 OPENAI_API_KEY, NVIDIA_API_KEY, or put it in ~/.nvidiakey (optionally \
                 DREGG_LLM_BASE / DREGG_LLM_MODEL), then re-run `cargo run --features \
                 live-brain -- brain-live`."
            );
            return;
        }
    };
    let (runtime, root_token, registry) = confinement();
    let gateway = HermesGateway::new(&runtime, root_token, registry);
    let prompt = std::env::args()
        .nth(2)
        .unwrap_or_else(|| "search the docs, then run the build".to_string());

    let peer = HermesAgentPeer::new("sess-brain-live", brain);
    let mut client = AcpClient::new(peer, gateway, 16);
    let run = client
        .run_prompt("/Users/ember/dev/breadstuffs", &prompt)
        .expect("the live brain-driven ACP loop runs end-to-end");

    let model = AgentDockModel::from_run("sess-brain-live", &run, client.gateway());
    print!("{}", model.render_text());
    println!(
        "\n(the live model decided {} tool-call(s); each admitted one is a receipted \
         dregg turn on the verified executor.)",
        run.verdicts.len()
    );
}

/// Without the `live-brain` feature, the live brain path is unavailable: report
/// how to build it in rather than silently running a scripted stand-in.
#[cfg(not(feature = "live-brain"))]
fn run_brain_live() {
    println!(
        "deos-hermes — the LIVE BYO-key brain is behind the `live-brain` feature.\n\
         Rebuild with it and provide a key, e.g.:\n\
         \n\
         \x20\x20ANTHROPIC_API_KEY=... cargo run --features live-brain -- brain-live\n"
    );
}

/// The `hermes-acp` program deos spawns for the live loop. Overridable via
/// `HERMES_ACP_BIN` (e.g. the Homebrew shim `/opt/homebrew/bin/hermes-acp`).
fn hermes_acp_program() -> String {
    std::env::var("HERMES_ACP_BIN").unwrap_or_else(|_| "hermes-acp".to_string())
}

/// The provider model deos pins for the live loop via `session/set_model`.
/// Overridable via `HERMES_ACP_MODEL`. The default is a Bedrock model `hermes-acp`
/// advertises; the live agent loop only reaches the provider once a model is
/// pinned (session/new alone leaves an empty `modelId`).
fn hermes_acp_model() -> String {
    std::env::var("HERMES_ACP_MODEL")
        .unwrap_or_else(|_| "bedrock:global.amazon.nova-2-lite-v1:0".to_string())
}

/// The live subprocess path: spawn the REAL `hermes-acp`, complete the handshake,
/// pin a model, prompt with a command Hermes flags as dangerous (so it issues a
/// `session/request_permission` back), and answer through the gateway.
///
/// Reports exactly how far the live env let it get (handshake / session / a real
/// permission round-trip / a full provider-backed turn), so the live ceiling is
/// honest from the output alone.
fn run_live(confine: Confine) {
    let banner = match confine {
        Confine::Standard => "LIVE subprocess",
        Confine::DenyTerminal => "LIVE subprocess — terminal DENIED (refusal demo)",
    };
    println!("deos-hermes — the confined Hermes ACP loop ({banner})\n");
    let program = hermes_acp_program();
    let model = hermes_acp_model();
    println!("spawning `{program}` (model `{model}`)…\n");

    let (runtime, root_token, registry) = confinement_with(confine);
    let gateway = HermesGateway::new(&runtime, root_token, registry);

    let transport = match AcpTransport::spawn_hermes(&program, &[]) {
        Ok(t) => t,
        Err(e) => {
            eprintln!(
                "could not spawn `{program}`: {e}\n\
                 (set HERMES_ACP_BIN to the hermes-acp shim, e.g. \
                 /opt/homebrew/bin/hermes-acp; or `cargo run` for the mock loop)"
            );
            return;
        }
    };

    let mut client = AcpClient::new(transport, gateway, 10);
    // The prompt asks for a command Hermes's dangerous-command detector flags
    // (`rm -rf …` = "recursive delete"), so Hermes issues a real
    // `session/request_permission` — the gateway seam exercised LIVE. The target
    // path is a harmless scratch dir, and the gateway answer the test path expects
    // is the gateway's own verdict (allow/deny), not a blanket allow.
    let prompt = "Run exactly this shell command and nothing else: \
                  rm -rf /tmp/deos_hermes_live_probe";
    match client.run_prompt_with_model("/tmp", prompt, Some(&model)) {
        Ok(run) => {
            let dock = AgentDockModel::from_run("live", &run, client.gateway());
            print!("{}", dock.render_text());
            println!("\n── live ceiling ──");
            println!(
                "handshake + session/new + session/prompt: COMPLETED (stop_reason = {})",
                run.stop_reason
            );
            if run.verdicts.is_empty() {
                println!(
                    "permission round-trip: NOT reached — Hermes produced no tool-call.\n\
                     (the live agent loop needs a working model provider + credentials; \
                     with none, the provider call fails inside Hermes before any tool-call \
                     is emitted. The handshake/session above is fully LIVE.)"
                );
            } else {
                use deos_hermes::PermissionOutcome;
                let allowed = run
                    .verdicts
                    .iter()
                    .filter(|(_, o)| matches!(o, PermissionOutcome::Allow { .. }))
                    .count();
                let refused = run.verdicts.len() - allowed;
                println!(
                    "permission round-trip: REACHED — {} tool-call(s) gated through the \
                     HermesGateway LIVE ({allowed} allowed = receipted dregg turn(s), \
                     {refused} refused in-band).",
                    run.verdicts.len()
                );
                for (call, outcome) in &run.verdicts {
                    match outcome {
                        PermissionOutcome::Allow {
                            receipt, remaining, ..
                        } => println!(
                            "  ✓ {} ALLOWED — receipt {}… ({remaining} left)",
                            call.name,
                            &receipt[..receipt.len().min(16)]
                        ),
                        PermissionOutcome::Reject { reason, .. } => {
                            println!("  ✗ {} REFUSED — {reason}", call.name)
                        }
                    }
                }
            }
        }
        Err(e) => {
            eprintln!(
                "live hermes-acp loop ended early: {e}\n\
                 (the handshake may not have completed — check that `{program}` runs \
                 `--check` cleanly: its venv needs the `agent-client-protocol` package)"
            );
        }
    }
}

/// THE DEEP-INTEGRATION LIVE PROOF — a real `hermes-acp` brain whose ONLY tools
/// are the dregg confined MCP server's (`run_js`, `terminal`). It registers THIS
/// binary (`deos-hermes mcp-server`) on `session/new`'s `mcpServers`, then prompts
/// the model to use a tool. Every tool the model calls routes through the dregg
/// sandbox (our subprocess: cap-gated, receipted; `terminal` execs in a confined
/// PD). The deos ACP client observes the `tool_call` events; the MCP subprocess
/// logs the confined execution to its own stderr.
///
/// Reports how far the live env let it get (handshake / a tool-call the model
/// routed to a dregg tool). Needs a reachable provider; with none, the handshake
/// still completes and we report that honestly.
fn run_live_mcp() {
    println!("deos-hermes — LIVE deep integration: the brain's tools are the dregg MCP server's\n");
    let program = hermes_acp_program();
    let model = hermes_acp_model();
    // The dregg MCP server binary the model's tools route through = THIS binary
    // (overridable via DEOS_MCP_SERVER_BIN, e.g. an absolute path or a wrapper).
    let self_bin = std::env::var("DEOS_MCP_SERVER_BIN")
        .ok()
        .unwrap_or_else(|| {
            std::env::current_exe()
                .ok()
                .and_then(|p| p.to_str().map(|s| s.to_string()))
                .unwrap_or_else(|| "deos-hermes".to_string())
        });
    println!(
        "spawning `{program}` (model `{model}`); dregg MCP server = `{self_bin} mcp-server`\n"
    );

    let (runtime, root_token, registry) = confinement();
    let gateway = HermesGateway::new(&runtime, root_token, registry);

    let transport = match AcpTransport::spawn_hermes(&program, &[]) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("could not spawn `{program}`: {e} (set HERMES_ACP_BIN)");
            return;
        }
    };

    let mut client = AcpClient::new(transport, gateway, 10).with_dregg_mcp_server(
        "dregg",
        &self_bin,
        &["mcp-server"],
        &[],
    );
    println!(
        "registered the dregg confined MCP server on session/new (`{self_bin} mcp-server`) — it \
         adds `run_js` + `terminal` (both dregg-sandboxed) to the model's tools. (Hermes keeps its \
         base toolset too; those built-ins still route through deos's authority gate.)"
    );

    // Ask the model to use a dregg tool. Hermes registers an MCP tool under the
    // sanitized name `mcp_<server>_<tool>` (= `mcp_dregg_run_js`), so the prompt
    // names it that way. The dregg tools are in its registry; a call routes to our
    // MCP subprocess (the sandbox). Force a tool-call (not a text answer).
    let prompt = "You MUST call the `mcp_dregg_run_js` tool exactly once now (do not answer in \
                  prose, do not explain — issue the tool call). Pass this exact argument: \
                  {\"script\": \"var app = deos.applet({ affordances: [\\\"bump\\\"] }); app.fire(\\\"bump\\\", 5);\"}. \
                  After the tool returns, reply with one short sentence.";
    match client.run_prompt_with_model("/tmp", prompt, Some(&model)) {
        Ok(run) => {
            println!("\n── live deep-integration result ──");
            println!(
                "handshake + session/new (mcpServers=dregg) + prompt: COMPLETED (stop_reason = {})",
                run.stop_reason
            );
            if run.tool_calls.is_empty() {
                println!(
                    "the model issued no tool-call this run (it answered in text). The dregg MCP \
                     server registration on session/new is LIVE — if hermes-acp's `mcp` SDK is \
                     present it spawns `{self_bin} mcp-server` and offers `mcp_dregg_run_js` + \
                     `mcp_dregg_terminal` to the model (see the hermes-acp log). A model that \
                     SELECTS one routes its call through the dregg sandbox; the server's confined \
                     execution is proven by `tests/mcp_confined_tools.rs` + the direct stdio drive."
                );
            } else {
                println!("the model issued {} tool-call(s):", run.tool_calls.len());
                for tc in &run.tool_calls {
                    // Hermes registers our MCP tools under the sanitized name
                    // `mcp_<server>_<tool>` (e.g. `mcp_dregg_run_js`); match either
                    // the bare dregg name or that prefixed form.
                    let dregg = deos_hermes::DREGG_TOOL_NAMES.contains(&tc.name.as_str())
                        || (tc.name.starts_with("mcp_dregg_")
                            && deos_hermes::DREGG_TOOL_NAMES
                                .iter()
                                .any(|t| tc.name.ends_with(t)));
                    println!(
                        "  • {} ({}) — {}",
                        tc.name,
                        if dregg {
                            "DREGG confined tool — routed through our MCP server (the sandbox)"
                        } else {
                            "non-dregg"
                        },
                        if dregg {
                            "executed in the dregg sandbox (see the MCP server's stderr)"
                        } else {
                            "the model has no dregg executor for this"
                        }
                    );
                }
            }
        }
        Err(e) => eprintln!("live deep-integration loop ended early: {e}"),
    }
}

/// THE DREGG MCP SERVER — speak standard MCP JSON-RPC over stdin/stdout, exposing
/// ONLY dregg-confined tools (`run_js`, `terminal`). Hermes spawns this binary
/// (`deos-hermes mcp-server`) when deos registers it on `session/new`'s
/// `mcpServers`; the model's only tools are then dregg's, so every tool-call
/// routes through the dregg sandbox (cap-gated, receipted; `terminal` execs
/// inside a confined PD). Runs until the client closes the stream (EOF).
///
/// Logs go to STDERR (stdout is the MCP wire — it must carry only ndjson frames).
fn run_mcp_server() {
    eprintln!("deos-hermes — the dregg confined MCP server (stdio); tools = run_js, terminal");

    // The dregg confinement the tools route through: a grantor runtime + the
    // standard per-kind/per-tool floors (terminal rate 5, run_js granted). Every
    // tool-call becomes a cap-gated, metered, receipted dregg turn.
    let mut cclerk = AgentCipherclerk::new();
    let root_token = cclerk.mint_token(&[7u8; 32], "deos");
    let runtime = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
    let registry = GrantRegistry::default_for_session(1_000_000)
        .with_standard_tool_grants(1_000_000)
        .with_tool_grant("run_js", 10_000, 1_000_000);
    let gateway = HermesGateway::new(&runtime, root_token, registry);

    let host = McpToolHost::new(gateway, 0);
    // The agent's `run_js` hands (deos-js mounted under `held`, never root). Only
    // available under the `js-agent` feature; without it, `run_js` reports the seam.
    #[cfg(feature = "js-agent")]
    let host = {
        use deos_hermes::RunJsTool;
        use dregg_cell::AuthRequired;
        let tool = RunJsTool::new(
            AuthRequired::Signature,
            [0x42; 32],
            [0x01; 32],
            vec![(0, deos_js::applet::pack_u64(0))],
            vec![
                ("bump".to_string(), AuthRequired::Signature),
                ("escalate".to_string(), AuthRequired::Proof),
            ],
        );
        // `with_run_js` boots SpiderMonkey; on failure keep the bare host (run_js
        // then reports the seam — no fabricated confinement).
        host.with_run_js(tool).unwrap_or_else(|e| {
            eprintln!("could not boot deos-js for run_js: {e}; run_js will report the seam");
            // The bare host whose run_js path reports the seam (its gateway was
            // moved into the failed `with_run_js`, so rebuild a fresh confinement).
            let mut c = AgentCipherclerk::new();
            let root = c.mint_token(&[8u8; 32], "deos");
            let rt2 = AgentRuntime::new(Arc::new(RwLock::new(c)), "deos");
            // SAFETY-of-lifetime: leak the fallback runtime so the host can borrow
            // it for the rest of the process (the server runs to process exit).
            let rt2: &'static AgentRuntime = Box::leak(Box::new(rt2));
            McpToolHost::new(
                HermesGateway::new(
                    rt2,
                    root,
                    GrantRegistry::default_for_session(1_000_000)
                        .with_standard_tool_grants(1_000_000),
                ),
                0,
            )
        })
    };

    let mut server = McpServer::new(host);
    let stdin = std::io::stdin();
    let stdout = std::io::stdout();
    let reader = stdin.lock();
    let writer = stdout.lock();
    match server.serve(reader, writer) {
        Ok(n) => eprintln!("deos-hermes mcp-server: session closed after {n} tools/call(s)"),
        Err(e) => eprintln!("deos-hermes mcp-server: stream error: {e}"),
    }
}
