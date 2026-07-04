//! DREGG-AS-HOST — the polarity inversion. dregg hosts the agent; the agent does
//! NOT host dregg.
//!
//! ## The polarity problem this fixes
//!
//! In [`crate::mcp_server`] (the prior slice) dregg's tools are registered INTO
//! hermes-acp's ACP session: hermes is the host, dregg's tools are guests added
//! alongside hermes's OWN base `[hermes-acp]` tools — and those base tools (an
//! unconfined `terminal` / `write_file`) are the leak. The authority gate
//! ([`crate::bridge`]) confines them at the *authority* face, but the agent
//! process itself still runs with full ambient OS authority.
//!
//! [`DreggHost`] inverts it. dregg is the host:
//!
//!   1. **The agent runs inside a dregg jail.** [`DreggHost::run_hosted_agent`]
//!      spawns the agent body INSIDE a confined firmament PD ([`crate::confined`])
//!      whose OS sandbox DENIES ambient file / exec / network and every inherited
//!      fd. The agent's ONLY channel is its firmament Endpoint — the dregg control
//!      channel. hermes's own base shell/file tools, run in this process, hit the
//!      jail walls (`open` denied, `socket` denied, `execve` denied) and go INERT.
//!      We do NOT fork hermes: the OS jail neutralizes the leaky base tools at the
//!      OS level, whatever the agent's tool table says.
//!   2. **dregg's tools are the only effective effect-path.** Inside the jail the
//!      agent's only way to *cause* anything is to send a dregg request over the
//!      Endpoint; the host routes it through [`crate::McpToolHost`] (cap-gated,
//!      receipted; `run_js` → a deos-js World, `terminal` → a nested confined PD).
//!      Every effect lands in OUR container, never the host.
//!   3. **Egress is a structured, opt-in door.** The host holds an
//!      [`EgressPolicy`]; sealed by default (no reach outside). When it grants a
//!      specific host subpath, THAT path — and only that path — becomes readable
//!      inside the jail (threaded into the sandbox profile). Revocable.
//!
//! ## What is REAL now — the brain runs IN the jail
//!
//! REAL: the JAIL (the OS sandbox — file/net/exec/fd denied, proven by the in-PD
//! probes), the EGRESS door (a granted host path readable, a sibling denied, both
//! proven in-PD), the dregg TOOL effect-path (cap-gated, receipted turns through
//! [`crate::HermesGateway`]), AND — the weld this file now carries — the AGENT
//! BRAIN itself, running INSIDE the confined PD.
//!
//! The jailed body is no longer a scripted probe suite. It is a REAL brain-driven
//! ACP peer ([`crate::HermesAgentPeer`] over the on-box [`crate::LocalBrain`])
//! COMPILED INTO the PD body: the exec-denied jail cannot `execve` a venv/subprocess,
//! so the brain's decision loop is in-process, and every tool-call it reaches for
//! crosses the firmament Endpoint as a `session/request_permission` the PARENT
//! answers through the [`crate::HermesGateway`] (which stays OUTSIDE the jail, on
//! the verified executor — a cap-gated, metered, receipted dregg turn, or an
//! in-band refusal the brain adapts to). The body ALSO still runs the jail/escape/
//! egress probes first (the confinement is unchanged), so a hosted run proves BOTH
//! that the agent is jailed AND that its brain thought its way to real receipts.
//!
//! THE ONE CONFINEMENT LIMITATION: the compiled-in brain is the on-box
//! [`crate::LocalBrain`] (it is `execve`-free and does no ambient I/O, so it fits
//! the jail). A *live* LLM brain ([`crate::HttpLlm`]) cannot run inside — it needs
//! the network the jail denies — so its provider call would have to ride a granted
//! egress socket (a structured door to exactly the provider), which is the next
//! slice. The BRAIN LOOP + the gate crossing are real today.

#![cfg(unix)]

use std::io::{Read, Write};
use std::os::unix::net::UnixStream;
use std::sync::{Arc, RwLock};

use crate::agent_peer::HermesAgentPeer;
use crate::brain::{LlmBrain, LocalBrain};
use crate::confined::{
    ConfinedAgent, can_connect_tcp, can_read_path, launch_confined_with_egress, probe,
};
use crate::egress::EgressPolicy;
use crate::{AcpClient, GrantRegistry, HermesGateway, PermissionOutcome};
use dregg_firmament::process_kernel::ProcessKernel;
use dregg_sdk::{AgentCipherclerk, AgentRuntime};

/// The default goal dregg's host drives a confined brain through when a caller
/// uses the gateway-less [`DreggHost::run_hosted_agent`] (the jail/escape/egress
/// proof). It names several tools so the on-box brain reaches for a search, a
/// write, a read, and a build — each a cap-gated receipted turn under the host's
/// default grants.
pub const DEFAULT_HOSTED_GOAL: &str =
    "search the docs, write a notes file, read the source, then run the build";

/// The cwd the host opens the confined session in (a sandboxed path — the jail
/// grants no real FS authority; this is only the session's nominal working dir).
const HOSTED_CWD: &str = "/sandboxed/cwd";

/// THE BASE-TOOL ESCAPE PROBES — the exact ambient reaches a leaky hermes base
/// tool would make, each one the jail must DENY. The hosted-agent body runs all
/// of them from inside the jail and folds the verdict; the host asserts every
/// escape was neutralized.
pub mod escape {
    /// An UNCONFINED shell — `execve` of `/bin/sh` — was DENIED (the jail has no
    /// exec authority, so hermes's `terminal` base tool cannot spawn a shell).
    pub const UNCONFINED_SHELL_DENIED: i32 = 0x100;
    /// A host-FS read OUTSIDE any grant — `open(/etc/passwd)` — was DENIED (the
    /// jail denies ambient file authority, so a `read_file` base tool is inert).
    pub const HOST_FS_READ_DENIED: i32 = 0x200;
    /// An ARBITRARY socket — `socket(AF_INET)` to a public address — was DENIED
    /// (the jail denies ambient network authority, so a `web` base tool is inert).
    pub const ARBITRARY_SOCKET_DENIED: i32 = 0x400;
    /// All three base-tool escapes neutralized.
    pub const ALL_NEUTRALIZED: i32 =
        UNCONFINED_SHELL_DENIED | HOST_FS_READ_DENIED | ARBITRARY_SOCKET_DENIED;
}

/// The verdict on one tool-call the confined brain reached for, as the gate (on
/// the verified executor, OUTSIDE the jail) decided it — the receipted-when-admitted
/// / refused-when-over-cap tooth, carried out of the jailed run.
#[derive(Clone, Debug)]
pub struct HostedToolVerdict {
    /// The tool the brain called.
    pub tool: String,
    /// `true` if the gate ADMITTED it (a receipted turn), `false` if refused.
    pub admitted: bool,
    /// The dregg receipt id (hex) on admit; `None` on refusal.
    pub receipt: Option<String>,
    /// The in-band refusal reason (the mandate leg that bit) on refuse; `None` on
    /// admit.
    pub reason: Option<String>,
}

/// The structured report a hosted-agent run produces — the proof, by running, that
/// dregg is the host AND that the agent's BRAIN ran inside the jail. Folds the
/// jailed body's confinement verdict together with the brain-driven ACP turn the
/// parent gated (goal in → receipted tool-calls → verdict).
#[derive(Clone, Debug, Default)]
pub struct HostedAgentReport {
    /// The raw verdict bitmask the jailed body folded ([`probe`] base teeth +
    /// [`escape`] neutralization teeth + [`probe::EGRESS_GRANTED_OPEN`] /
    /// [`probe::EGRESS_SIBLING_DENIED`]).
    pub verdict: i32,
    /// Whether the FOUR base jail teeth held (file/net/exec/extra-fd denied, the
    /// Endpoint live) — the agent is jailed.
    pub jailed: bool,
    /// Whether ALL THREE base-tool escapes were neutralized (unconfined shell /
    /// host-FS read / arbitrary socket each denied by the jail).
    pub base_tools_neutralized: bool,
    /// Whether the GRANTED egress door was open inside the jail (only meaningful
    /// when the policy granted a path).
    pub egress_granted_open: bool,
    /// Whether a path OUTSIDE the grant stayed denied (the door is specific, not a
    /// hole).
    pub egress_sibling_denied: bool,
    /// Whether the GRANTED provider SOCKET door was reachable inside the jail (the
    /// jailed brain could `connect` to exactly the granted host:port). Only
    /// meaningful when the policy granted a provider endpoint.
    pub egress_net_granted_open: bool,
    /// Whether an outbound connect to a host:port OUTSIDE the grant stayed denied
    /// (the socket door is to a specific endpoint, not "the network").
    pub egress_net_sibling_denied: bool,
    /// The confined brain's streamed final text (the agent's own account of its
    /// turn) — proof the brain ran, not a script.
    pub agent_text: String,
    /// The ACP `stop_reason` the turn ended on.
    pub stop_reason: String,
    /// The gate's verdict on every tool-call the confined brain reached for — each
    /// a real receipt (admitted) or an in-band refusal (over-cap), decided on the
    /// verified executor OUTSIDE the jail.
    pub tool_verdicts: Vec<HostedToolVerdict>,
}

impl HostedAgentReport {
    fn from_run(verdict: i32, run: crate::acp_client::PromptRun) -> HostedAgentReport {
        let tool_verdicts = run
            .verdicts
            .into_iter()
            .map(|(call, outcome)| match outcome {
                PermissionOutcome::Allow { receipt, .. } => HostedToolVerdict {
                    tool: call.name,
                    admitted: true,
                    receipt: Some(receipt),
                    reason: None,
                },
                PermissionOutcome::Reject { reason, .. } => HostedToolVerdict {
                    tool: call.name,
                    admitted: false,
                    receipt: None,
                    reason: Some(reason),
                },
            })
            .collect();
        HostedAgentReport {
            verdict,
            jailed: verdict & probe::ALL == probe::ALL,
            base_tools_neutralized: verdict & escape::ALL_NEUTRALIZED == escape::ALL_NEUTRALIZED,
            egress_granted_open: verdict & probe::EGRESS_GRANTED_OPEN != 0,
            egress_sibling_denied: verdict & probe::EGRESS_SIBLING_DENIED != 0,
            egress_net_granted_open: verdict & probe::EGRESS_NET_GRANTED_OPEN != 0,
            egress_net_sibling_denied: verdict & probe::EGRESS_NET_SIBLING_DENIED != 0,
            agent_text: run.agent_text,
            stop_reason: run.stop_reason,
            tool_verdicts,
        }
    }

    /// How many tool-calls the gate ADMITTED (each a receipted turn).
    pub fn admitted_count(&self) -> usize {
        self.tool_verdicts.iter().filter(|v| v.admitted).count()
    }

    /// How many tool-calls the gate REFUSED in-band (over-cap).
    pub fn refused_count(&self) -> usize {
        self.tool_verdicts.iter().filter(|v| !v.admitted).count()
    }

    /// The hex receipt id of every admitted tool-call — the real receipts the
    /// confined brain's turn left on the verified executor.
    pub fn receipts(&self) -> Vec<&str> {
        self.tool_verdicts
            .iter()
            .filter_map(|v| v.receipt.as_deref())
            .collect()
    }
}

/// DREGG, THE HOST. Holds the egress policy (the doors it grants the agent) and
/// spawns the agent INTO a dregg jail whose only channel is the dregg control
/// Endpoint. The dregg tool effect-path is driven by the caller over the returned
/// [`ConfinedAgent`]'s Endpoint (the same transport the confined-launch tests use)
/// and/or asserted directly via [`crate::McpToolHost`].
pub struct DreggHost {
    /// The structured egress doors this host grants the jailed agent. Sealed (no
    /// doors) by default; opened/closed with [`EgressPolicy::grant_read`] /
    /// [`EgressPolicy::revoke`].
    pub egress: EgressPolicy,
}

impl Default for DreggHost {
    fn default() -> Self {
        DreggHost::new()
    }
}

impl DreggHost {
    /// A new dregg host with a SEALED egress policy (the agent reaches the outside
    /// only through dregg's tools, which route to our containers).
    pub fn new() -> DreggHost {
        DreggHost {
            egress: EgressPolicy::sealed(),
        }
    }

    /// GRANT the jailed agent a structured, revocable read-door to one host
    /// subpath. The next jail this host spawns threads exactly this path into its
    /// sandbox profile; nothing else opens. (Builder form for ergonomics.)
    pub fn with_egress_read(mut self, path: impl Into<String>) -> DreggHost {
        self.egress.grant_read(path);
        self
    }

    /// GRANT the jailed agent the structured, revocable SOCKET door to EXACTLY one
    /// provider `host:port` — the provider-only egress. The next jail this host
    /// spawns threads exactly this outbound endpoint into its sandbox profile; a
    /// jailed LIVE brain's model call rides it, and no other host/port opens.
    /// (Builder form.)
    pub fn with_egress_provider(mut self, host: impl Into<String>, port: u16) -> DreggHost {
        self.egress.grant_provider(host, port);
        self
    }

    /// GRANT the provider socket door derived from a base URL (e.g.
    /// `https://api.anthropic.com` → `api.anthropic.com:443`). The exact shape the
    /// host uses to open a door to where a LIVE brain is configured to call.
    pub fn with_egress_provider_url(mut self, base_url: &str) -> DreggHost {
        self.egress.grant_provider_url(base_url);
        self
    }

    /// SPAWN the agent INTO a dregg jail and drive its BRAIN — the run-by-running
    /// proof of the polarity inversion AND that the mind runs where the scripted
    /// body used to. Uses a DEFAULT host-owned confined gateway (dregg the host
    /// mints its own root grant + standard tool floors) and the
    /// [`DEFAULT_HOSTED_GOAL`]; for a caller-supplied gateway/goal (e.g. to prove a
    /// tool refused over-cap) use [`DreggHost::run_hosted_agent_with`].
    ///
    /// The jail's sandbox profile is THIS host's egress policy (sealed ⇒ no door; a
    /// grant ⇒ exactly that read path). Inside the jail the agent body runs the base
    /// jail probes, the base-tool-escape probes, and the egress probes (the agent IS
    /// jailed, the base tools ARE neutralized, the door is specific), THEN serves a
    /// real brain-driven ACP turn whose every tool-call the parent gates.
    pub fn run_hosted_agent(
        &self,
        kernel: &ProcessKernel,
        granted_egress_probe: Option<&str>,
        ungranted_egress_probe: Option<&str>,
    ) -> std::io::Result<HostedAgentReport> {
        // dregg THE HOST owns the grantor: it mints a root token, stands up a
        // runtime, and confines the session under the standard per-tool floors.
        let mut cclerk = AgentCipherclerk::new();
        let root = cclerk.mint_token(&[7u8; 32], "deos-host");
        let runtime = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos-host");
        let registry =
            GrantRegistry::default_for_session(1_000_000).with_standard_tool_grants(1_000_000);
        let gateway = HermesGateway::new(&runtime, root, registry);
        self.run_hosted_agent_with(
            kernel,
            gateway,
            DEFAULT_HOSTED_GOAL,
            granted_egress_probe,
            ungranted_egress_probe,
        )
    }

    /// As [`DreggHost::run_hosted_agent`], but with a CALLER-SUPPLIED gateway + goal
    /// — the real hosted-run API. `gateway` is the cap-gated, receipted enforcement
    /// point on the verified executor (it stays OUTSIDE the jail); `goal` is the
    /// prompt the confined brain reasons over. A gateway that denies a tool proves
    /// the refused-when-over-cap tooth; the standard floors prove
    /// receipted-when-admitted.
    ///
    /// The confined brain ([`crate::LocalBrain`], compiled into the PD body) drives
    /// the turn; each tool-call crosses the firmament Endpoint as a
    /// `session/request_permission` this `gateway` decides. Returns the folded
    /// [`HostedAgentReport`] (confinement verdict + the brain's gated tool-calls +
    /// their real receipts).
    pub fn run_hosted_agent_with(
        &self,
        kernel: &ProcessKernel,
        gateway: HermesGateway<'_>,
        goal: &str,
        granted_egress_probe: Option<&str>,
        ungranted_egress_probe: Option<&str>,
    ) -> std::io::Result<HostedAgentReport> {
        self.run_brain_confined(
            kernel,
            gateway,
            goal,
            granted_egress_probe,
            ungranted_egress_probe,
            None,
            None,
            LocalBrain::new(),
        )
    }

    /// As [`DreggHost::run_hosted_agent_with`], but the jailed brain ALSO probes the
    /// structured SOCKET door: `granted_net`/`ungranted_net` are `(host, port)` the
    /// body tries to `connect` to from inside the jail. The GRANTED endpoint (the
    /// one this host opened with [`DreggHost::with_egress_provider`]) must be
    /// reachable; an UNGRANTED one must stay EPERM'd. Still an on-box
    /// [`LocalBrain`] — the crisp OS-level proof that the provider-only door opens
    /// exactly one endpoint (the LIVE brain riding it is
    /// [`DreggHost::run_hosted_agent_live`]).
    pub fn run_hosted_agent_net(
        &self,
        kernel: &ProcessKernel,
        gateway: HermesGateway<'_>,
        goal: &str,
        granted_net: Option<(&str, u16)>,
        ungranted_net: Option<(&str, u16)>,
    ) -> std::io::Result<HostedAgentReport> {
        self.run_brain_confined(
            kernel,
            gateway,
            goal,
            None,
            None,
            granted_net,
            ungranted_net,
            LocalBrain::new(),
        )
    }

    /// RUN A LIVE BRAIN IN THE JAIL — the real model drives the confined ACP loop,
    /// its completion call riding the provider-only egress socket door while
    /// execve / open / all other network stay denied.
    ///
    /// This is the slice past on-box confinement: [`crate::brain::HttpLlm`] (built
    /// from the env via [`crate::brain::live_brain_from_env`]) runs INSIDE the
    /// exec-denied PD. Its provider request rides the socket door THIS host must
    /// have opened ([`DreggHost::with_egress_provider_url`] pointed at the same
    /// base URL the brain calls); every tool-call the model then reaches for still
    /// crosses the Endpoint to the gateway (cap-gated, receipted) — the gate is
    /// unchanged. `granted_net`/`ungranted_net` fold the same crisp socket-door
    /// teeth as [`DreggHost::run_hosted_agent_net`].
    ///
    /// OFF by default: if NO BYO key is configured, there is no live brain, so this
    /// falls back to the on-box [`LocalBrain`] (the default hosted run — no network
    /// used even if a door is open). Only a configured key + provider door puts a
    /// live model on the socket.
    #[cfg(feature = "live-brain")]
    pub fn run_hosted_agent_live(
        &self,
        kernel: &ProcessKernel,
        gateway: HermesGateway<'_>,
        goal: &str,
        granted_net: Option<(&str, u16)>,
        ungranted_net: Option<(&str, u16)>,
    ) -> std::io::Result<HostedAgentReport> {
        match crate::brain::live_brain_from_env() {
            Some(brain) => self.run_brain_confined(
                kernel,
                gateway,
                goal,
                None,
                None,
                granted_net,
                ungranted_net,
                brain,
            ),
            // No key → stay on the on-box brain (off-by-default): the door may be
            // open but no live model is put on it.
            None => self.run_hosted_agent_net(kernel, gateway, goal, granted_net, ungranted_net),
        }
    }

    /// THE GENERIC CONFINED-BRAIN CORE — launch `brain` into the dregg jail (with
    /// THIS host's egress policy folded into the sandbox profile), read the
    /// confinement verdict, drive the brain-turn through `gateway`, reap, and fold
    /// the report. Generic over the brain so the SAME jail/drive/receipt rail runs
    /// the on-box [`LocalBrain`] or a live [`crate::brain::HttpLlm`].
    #[allow(clippy::too_many_arguments)]
    fn run_brain_confined<B: LlmBrain>(
        &self,
        kernel: &ProcessKernel,
        gateway: HermesGateway<'_>,
        goal: &str,
        granted_egress_probe: Option<&str>,
        ungranted_egress_probe: Option<&str>,
        granted_net: Option<(&str, u16)>,
        ungranted_net: Option<(&str, u16)>,
        brain: B,
    ) -> std::io::Result<HostedAgentReport> {
        let granted = granted_egress_probe.map(|s| s.to_string());
        let ungranted = ungranted_egress_probe.map(|s| s.to_string());
        let granted_net = granted_net.map(|(h, p)| (h.to_string(), p));
        let ungranted_net = ungranted_net.map(|(h, p)| (h.to_string(), p));
        let agent: ConfinedAgent =
            launch_confined_with_egress(kernel, &self.egress, move |sock| {
                brain_body_serving(
                    sock,
                    "sess-hosted",
                    granted.as_deref(),
                    ungranted.as_deref(),
                    granted_net.as_ref().map(|(h, p)| (h.as_str(), *p)),
                    ungranted_net.as_ref().map(|(h, p)| (h.as_str(), *p)),
                    brain,
                )
            })?;

        // (1) The body emits its FULL confinement verdict as ONE JSON line BEFORE it
        //     begins serving ACP (the line carries the escape/egress teeth the 8-bit
        //     exit code cannot). Read exactly that one line off the Endpoint — byte
        //     by byte, so we never over-read into the ACP frames that follow.
        let endpoint_verdict = read_jail_verdict_line(&agent.pd.kernel_sock).unwrap_or(0);

        // (2) DRIVE the confined brain over the SAME Endpoint: the UNCHANGED client
        //     answers every tool-call through the gateway (the verified executor,
        //     outside the jail) → real receipts / in-band refusals.
        let run = {
            let transport = agent
                .transport()
                .map_err(|e| std::io::Error::other(e.to_string()))?;
            let mut client = AcpClient::new(transport, gateway, 100);
            client
                .run_prompt(HOSTED_CWD, goal)
                .map_err(|e| std::io::Error::other(e.to_string()))?
            // client (and its Endpoint clone) drop here, before we reap the child.
        };

        // (3) Reap the child's exit code (the base jail teeth as a cross-check) and
        //     fold everything into the report.
        let exit_verdict = agent.join_verdict()?;
        Ok(HostedAgentReport::from_run(
            endpoint_verdict | (exit_verdict & probe::ALL),
            run,
        ))
    }
}

/// Read exactly ONE newline-terminated JSON line off the confined child's Endpoint
/// — the `{"jailVerdict":N}` line the body emits before it serves ACP — and return
/// `N`. Reads BYTE BY BYTE (not buffered) so it consumes only up to the newline and
/// leaves the ACP frames that follow untouched on the socket for
/// [`ConfinedAgent::transport`] to drive.
fn read_jail_verdict_line(sock: &UnixStream) -> Option<i32> {
    let mut reader = sock.try_clone().ok()?;
    let mut line: Vec<u8> = Vec::with_capacity(64);
    let mut byte = [0u8; 1];
    loop {
        match reader.read(&mut byte) {
            Ok(0) => break, // EOF before a newline.
            Ok(_) => {
                if byte[0] == b'\n' {
                    break;
                }
                line.push(byte[0]);
            }
            Err(_) => return None,
        }
    }
    let v: serde_json::Value = serde_json::from_slice(&line).ok()?;
    v.get("jailVerdict")
        .and_then(|x| x.as_i64())
        .map(|n| n as i32)
}

/// THE JAILED AGENT BODY — runs INSIDE the dregg jail (confinement already applied:
/// file/other-net/exec denied, every non-Endpoint fd closed). It (1) proves the jail
/// neutralizes the leaky base tools + honors the file AND socket egress doors, (2)
/// emits that confinement verdict as one line, then (3) SERVES `brain` — the on-box
/// [`LocalBrain`] OR a live [`crate::brain::HttpLlm`] — over the Endpoint, its
/// tool-calls crossing to the parent's gateway. The brain's DECISION loop runs
/// in-process (the exec-denied jail cannot spawn a subprocess); a LIVE brain's
/// provider call rides the GRANTED socket door and nothing else; only tool-calls
/// leave, and only through the gate.
///
/// `granted_net`/`ungranted_net` are `(host, port)` the body probes with a raw
/// `connect(2)`: the granted provider endpoint must be reachable (the socket door
/// is open), an ungranted one must stay EPERM'd (the door is specific).
fn brain_body_serving<B: LlmBrain>(
    sock: &mut UnixStream,
    session_id: &str,
    granted_egress: Option<&str>,
    ungranted_egress: Option<&str>,
    granted_net: Option<(&str, u16)>,
    ungranted_net: Option<(&str, u16)>,
    brain: B,
) -> i32 {
    // (1) The four base jail teeth (file/net denied, one fd — probe BEFORE the serve
    //     loop clones the Endpoint, so exactly one non-std fd is open).
    let mut verdict = crate::confined::run_sandbox_probes();

    // (2) THE BASE-TOOL ESCAPES — exactly the ambient reaches a leaky hermes base
    //     tool would make. Each must be DENIED by the jail.
    //   • an unconfined shell (hermes `terminal`): execve(/bin/sh) — no exec auth.
    if !can_execve_shell() {
        verdict |= escape::UNCONFINED_SHELL_DENIED;
    }
    //   • a host-FS read outside any grant (hermes `read_file`): open(/etc/passwd).
    if !can_read_path("/etc/passwd") {
        verdict |= escape::HOST_FS_READ_DENIED;
    }
    //   • an arbitrary socket (hermes `web`): socket(AF_INET) — already folded as
    //     NET_DENIED by run_sandbox_probes; mirror it into the escape tooth so the
    //     report reads as "base web tool neutralized".
    if verdict & probe::NET_DENIED != 0 {
        verdict |= escape::ARBITRARY_SOCKET_DENIED;
    }

    // (3) THE STRUCTURED EGRESS — the host wired (or didn't) a specific door.
    //   • the GRANTED path must be readable (the door is open).
    if let Some(p) = granted_egress
        && can_read_path(p)
    {
        verdict |= probe::EGRESS_GRANTED_OPEN;
    }
    //   • a path OUTSIDE the grant must STILL be denied (specific door, not a hole).
    if let Some(p) = ungranted_egress
        && !can_read_path(p)
    {
        verdict |= probe::EGRESS_SIBLING_DENIED;
    }

    // (3b) THE STRUCTURED SOCKET EGRESS — the provider-only network door.
    //   • the GRANTED provider endpoint must be reachable (the socket door is open).
    if let Some((h, p)) = granted_net
        && can_connect_tcp(h, p)
    {
        verdict |= probe::EGRESS_NET_GRANTED_OPEN;
    }
    //   • a host:port OUTSIDE the grant must STILL be denied (specific door, not
    //     "the network"): the jail EPERMs the connect.
    if let Some((h, p)) = ungranted_net
        && !can_connect_tcp(h, p)
    {
        verdict |= probe::EGRESS_NET_SIBLING_DENIED;
    }

    // (4) EMIT the full confinement verdict as ONE line the parent reads before it
    //     drives ACP (the line carries the escape/egress teeth the 8-bit exit code
    //     cannot). IPC_WORKS is set optimistically here; the exit code below sets it
    //     only if the ACP serve actually ran (the honest cross-check).
    let reported = verdict | probe::IPC_WORKS;
    let line = format!("{{\"jailVerdict\":{reported}}}\n");
    let _ = sock.write_all(line.as_bytes()).and_then(|_| sock.flush());

    // (5) SERVE THE REAL BRAIN over the Endpoint — the compiled-in on-box brain
    //     decides in-process; every tool-call crosses to the parent's gateway. The
    //     serve returns the instant the brain's turn completes.
    let mut peer = HermesAgentPeer::new(session_id, brain);
    let served =
        crate::confined::serve_acp_peer_over_endpoint(sock, &mut peer, |p| p.turn_complete())
            .is_ok();
    if served {
        verdict |= probe::IPC_WORKS;
    }
    verdict & probe::ALL
}

/// Attempt the ambient reach a leaky `terminal` base tool needs: `execve` an
/// unconfined shell. Returns whether it SUCCEEDED. Under the jail (no exec
/// authority — macOS `process-exec*` denied / Linux seccomp `execve` EPERM) it
/// must fail (false). We `fork` so a (denied) exec never replaces THIS process;
/// the child reports exec success/failure via its exit code.
fn can_execve_shell() -> bool {
    let pid = unsafe { libc::fork() };
    if pid < 0 {
        // Can't even fork under the jail — certainly can't spawn a shell.
        return false;
    }
    if pid == 0 {
        // CHILD: try to become /bin/sh. If execve returns, it FAILED (denied);
        // exit 1. If it succeeds we never reach the exit (but the jail denies it).
        let path = b"/bin/sh\0";
        let arg0 = b"sh\0";
        let argv = [arg0.as_ptr() as *const libc::c_char, std::ptr::null()];
        unsafe {
            libc::execv(path.as_ptr() as *const libc::c_char, argv.as_ptr());
            // execv returned ⇒ denied.
            libc::_exit(1);
        }
    }
    // PARENT: reap the child. exit 0 would mean exec succeeded (it cannot under the
    // jail); any non-zero / signal ⇒ exec was denied. The jail also denies the
    // `fork` path's child its own exec, so this is belt-and-suspenders.
    let mut status: libc::c_int = 0;
    unsafe {
        libc::waitpid(pid, &mut status, 0);
    }
    // WIFEXITED && status==0 would be exec success; anything else = denied.

    libc::WIFEXITED(status) && libc::WEXITSTATUS(status) == 0
}
