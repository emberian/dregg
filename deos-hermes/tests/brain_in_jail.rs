//! BRAIN-IN-JAIL — the real agent brain runs INSIDE the deos-hermes confined PD.
//!
//! The two confinement stacks are merged: the OS jail that used to run a scripted
//! probe suite now runs a REAL brain-driven ACP peer ([`HermesAgentPeer`] over the
//! on-box [`LocalBrain`]) COMPILED INTO the PD body. The brain decides in-process
//! (the exec-denied jail cannot spawn a subprocess); every tool-call it reaches for
//! crosses the firmament Endpoint as a `session/request_permission` the PARENT
//! answers through the [`HermesGateway`] on the verified executor — OUTSIDE the jail.
//!
//! Run: `cd deos-hermes && cargo test --test brain_in_jail`
//!
//! The teeth:
//!   1. THE JAIL STILL DENIES — the brain body ALSO ran the base + escape probes:
//!      execve / open(/etc/passwd) / socket(AF_INET) each denied from inside.
//!   2. RECEIPTS STILL FLOW — the confined brain's admitted tool-calls each left a
//!      real hex dregg receipt (a committed metered turn on the verified executor).
//!   3. THE GATE STILL BITES — a tool over-cap is REFUSED in-band while a granted
//!      one is RECEIPTED, both decided across the Endpoint by the outside gateway.

#![cfg(unix)]

use std::sync::{Arc, RwLock};

use deos_hermes::host::escape;
use deos_hermes::{DreggHost, GrantRegistry, HermesGateway};
use dregg_firmament::process_kernel::ProcessKernel;
use dregg_sdk::{AgentCipherclerk, AgentRuntime, HeldToken};

fn grantor() -> (AgentRuntime, HeldToken) {
    let mut cclerk = AgentCipherclerk::new();
    let root = cclerk.mint_token(&[7u8; 32], "deos");
    let rt = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
    (rt, root)
}

/// (1)+(2) A confined BRAIN-DRIVEN run: the agent is jailed AND its brain thought
/// its way to real receipts. dregg the host owns a default gateway (standard
/// floors), so every tool the on-box brain reaches for is admitted + receipted.
#[test]
fn confined_brain_run_is_jailed_and_leaves_real_receipts() {
    let kernel = ProcessKernel::new();
    let host = DreggHost::new(); // sealed egress — the pure jail.

    let report = host
        .run_hosted_agent(&kernel, None, None)
        .expect("spawn the brain into the dregg jail and drive its turn");

    // THE JAIL STILL DENIES — the brain body ran the base + escape probes first.
    assert!(
        report.jailed,
        "the brain is jailed (file/net/exec/extra-fd denied); verdict=0x{:x}",
        report.verdict
    );
    assert!(
        report.base_tools_neutralized,
        "execve / host-FS read / arbitrary socket each denied from inside the jail; \
         verdict=0x{:x}",
        report.verdict
    );
    assert_eq!(
        report.verdict & escape::ALL_NEUTRALIZED,
        escape::ALL_NEUTRALIZED,
        "every base-tool escape neutralized at the OS level; verdict=0x{:x}",
        report.verdict
    );

    // THE BRAIN RAN — a real multi-step turn, not a script: the on-box brain read
    // the goal, reached for several tools, and summarized.
    assert_eq!(report.stop_reason, "end_turn");
    assert!(
        report.agent_text.contains("thinking"),
        "the confined brain streamed its own reply: {:?}",
        report.agent_text
    );
    assert!(
        report.tool_verdicts.len() >= 2,
        "the brain drove a multi-step turn, got {} tool-calls",
        report.tool_verdicts.len()
    );

    // RECEIPTS STILL FLOW — every admitted tool-call left a real 64-hex dregg
    // receipt, a committed metered turn on the verified executor OUTSIDE the jail.
    assert!(
        report.admitted_count() >= 2,
        "the brain's tool-calls were admitted + receipted, got {} admits",
        report.admitted_count()
    );
    let receipts = report.receipts();
    assert_eq!(
        receipts.len(),
        report.admitted_count(),
        "every admitted tool-call carries a receipt"
    );
    for r in &receipts {
        assert_eq!(r.len(), 64, "a real hex receipt id: {r}");
        assert!(r.chars().all(|c| c.is_ascii_hexdigit()), "hex receipt: {r}");
    }
}

/// (3) THE GATE STILL BITES across the Endpoint — a caller-supplied gateway that
/// denies `write_file` refuses that call in-band while granted tools are receipted,
/// and the brain (inside the jail) adapts to the refusal. The whole decision is
/// made OUTSIDE the jail, on the verified executor.
#[test]
fn confined_tool_call_is_gated_refused_over_cap_receipted_when_admitted() {
    let kernel = ProcessKernel::new();
    let host = DreggHost::new();

    let (rt, root) = grantor();
    // Deny `write_file` outright (rate 0); everything else within the floors.
    let registry = GrantRegistry::default_for_session(1_000_000)
        .with_standard_tool_grants(1_000_000)
        .with_grant_for_tool_deny("write_file");
    let gateway = HermesGateway::new(&rt, root, registry);

    let report = host
        .run_hosted_agent_with(
            &kernel,
            gateway,
            "write a notes file and run the build",
            None,
            None,
        )
        .expect("drive the confined brain through a partially-denying gateway");

    // Still jailed around the gated turn.
    assert!(
        report.jailed,
        "still jailed; verdict=0x{:x}",
        report.verdict
    );

    // THE GATE REFUSED the over-cap tool in-band, naming the leg that bit…
    let refused = report
        .tool_verdicts
        .iter()
        .find(|v| v.tool == "write_file")
        .expect("the brain reached for write_file");
    assert!(
        !refused.admitted,
        "write_file outside caps must be refused across the Endpoint"
    );
    let reason = refused.reason.as_deref().unwrap_or("");
    assert!(
        reason.contains("scope") || reason.contains("rate"),
        "the in-band refusal names the leg that bit: {reason}"
    );

    // …the brain ADAPTED (reached the denied tool exactly once) and a GRANTED tool
    // still committed a real receipted turn.
    let write_calls = report
        .tool_verdicts
        .iter()
        .filter(|v| v.tool == "write_file")
        .count();
    assert_eq!(write_calls, 1, "the brain did not bang on the denied tool");
    assert!(
        report.admitted_count() >= 1,
        "a granted tool still committed a receipted turn under partial confinement"
    );
    assert!(
        report.receipts().iter().all(|r| r.len() == 64),
        "each admitted call carries a real receipt"
    );
    assert!(
        report.refused_count() >= 1,
        "the over-cap tool was refused in-band"
    );
}
