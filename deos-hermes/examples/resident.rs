//! THE RESIDENT, HEADLESS — a real confined agent living under an attenuated
//! mandate, driven end-to-end with zero gpui, zero mozjs, zero network.
//!
//! Run it anywhere (the orchestrator's remote box, an offline laptop):
//!
//! ```text
//! cd deos-hermes && cargo run --example resident
//! ```
//!
//! What it proves, on the SAME rail the desktop dock drives:
//!
//!   * a REAL brain ([`deos_hermes::LocalBrain`] by default; a BYO-key
//!     [`deos_hermes::HttpLlm`] if `ANTHROPIC_API_KEY` / `HERMES_API_KEY` is set)
//!     forms a plan from the prompt and issues tool-calls one at a time;
//!   * every admitted call is a cap-gated, metered, RECEIPTED dregg turn on the
//!     verified executor (each `Allow` carries a real 64-hex receipt id +
//!     remaining budget);
//!   * an over-reach is REFUSED IN-BAND — the attenuated mandate denies
//!     `write_file`, so the write the brain reaches for is refused with the leg
//!     that bit, and the brain ADAPTS (it falls back to a read-only probe, never
//!     bangs on the denied tool);
//!   * a small `terminal` rate ceiling bounds the most visceral tool.
//!
//! This is the "resident" phase-1 acceptance the desktop Agent Room will later
//! render on glass. Here it is naked: verdicts printed, invariants asserted.

use std::sync::{Arc, RwLock};

use deos_hermes::{
    AcpClient, AgentCipherclerk, AgentRuntime, GrantRegistry, HeldToken, HermesAgentPeer,
    HermesGateway, PermissionOutcome, resident_brain_from_env,
};

fn main() {
    // deos is the grantor: it holds a root token on a runtime and confines the
    // session under an ATTENUATED mandate.
    let mut cclerk = AgentCipherclerk::new();
    let root: HeldToken = cclerk.mint_token(&[7u8; 32], "deos");
    let runtime = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");

    // THE ATTENUATED MANDATE + SMALL BUDGET: the standard confinement floors, but
    // `write_file` is DENIED outright (rate 0 → a guaranteed in-band refusal) and
    // `terminal` is held to a tight rate-5 ceiling (a call budget on the hands).
    let registry = GrantRegistry::default_for_session(1_000)
        .with_standard_tool_grants(1_000)
        .with_grant_for_tool_deny("write_file")
        .with_tool_grant("terminal", 5, 1_000);
    let gateway = HermesGateway::new(&runtime, root, registry);

    // The resident's brain — on-box by default (hermetic), BYO-key when present.
    let brain = resident_brain_from_env();
    println!("resident brain: {}", brain.describe());
    let peer = HermesAgentPeer::new("resident-demo", brain);
    let mut client = AcpClient::new(peer, gateway, 100);

    // A prompt whose verbs make the brain plan search + read + write + build/test.
    let prompt =
        "search the docs, read the source, write a notes file, then run the build and tests";
    let run = client
        .run_prompt("/deos/resident", prompt)
        .expect("the confined resident loop runs end-to-end");

    println!("\n── gate verdicts ──────────────────────────────────────────────");
    let mut receipted = 0usize;
    let mut refused = 0usize;
    for (call, outcome) in &run.verdicts {
        match outcome {
            PermissionOutcome::Allow {
                receipt, remaining, ..
            } => {
                receipted += 1;
                let head = &receipt[..8.min(receipt.len())];
                println!("  ✓ {:<12} receipt {head}…  {remaining} left", call.name);
            }
            PermissionOutcome::Reject { reason, .. } => {
                refused += 1;
                println!("  ✗ {:<12} REFUSED — {reason}", call.name);
            }
        }
    }
    println!("───────────────────────────────────────────────────────────────\n");
    println!("agent: {}", run.agent_text.trim());

    // The acceptance invariants (the orchestrator's remote run enforces these).
    assert!(
        receipted >= 1,
        "the resident committed at least one real receipted turn"
    );
    assert!(
        refused >= 1,
        "the attenuated mandate refused at least one call in-band"
    );
    assert!(
        run.verdicts
            .iter()
            .any(|(c, o)| c.name == "write_file" && matches!(o, PermissionOutcome::Reject { .. })),
        "the denied write_file was the in-band refusal"
    );
    // The metered write worker committed ZERO turns — the refusal was real (no
    // turn, no spend), not a cosmetic label.
    assert_eq!(
        client.gateway().calls_made_for_tool("write_file"),
        0,
        "a refused tool commits no metered turn"
    );

    println!(
        "\nresident: {receipted} receipted turn(s), {refused} in-band refusal(s) — \
         every surface a live World read, every actuation a verified turn."
    );
}
