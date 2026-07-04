//! `grain-demo` — the seed of the in-browser renter check.
//!
//! Drive a hosted session, produce the [`GrainAttestation`] a host hands back,
//! and verify it AS A RENTER, re-running nothing. The flow the WASM renter-check
//! runs: pin *(signer, tip)*, call `GrainAttestation::verify`, read off the R0
//! verdict — tamper-evidence under the pinned signer — with the honest boundary
//! (R1/R2 rungs, R3 gap) printed alongside.
//!
//! Run: `cargo run -p grain-verify --bin grain-demo`.

use dregg_agent::agent::{AgentAction, AgentSpec, PlannedBrain, ToolCall};
use dregg_agent::session::Session;
use dregg_agent::toolkit::Toolkit;
use dregg_agent::tools::{OperatorTools, ShellOut};
use grain_verify::{GrainAttestation, WHOLE_HISTORY_GAP};
use std::path::Path;

fn shell_plan(cmds: &[&str]) -> PlannedBrain {
    PlannedBrain::new(
        cmds.iter()
            .map(|c| AgentAction::Op(ToolCall::new("shell", [("cmd".to_string(), c.to_string())])))
            .collect(),
    )
}

fn main() {
    // ── the HOST side: drive a confined session over a budget ─────────────────
    let dir = std::env::temp_dir().join(format!("grain-demo-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let toolkit = OperatorTools::new(Toolkit::new(), &dir).with_shell(|cmd: &str, _cwd: &Path| {
        Ok(ShellOut {
            exit: 0,
            stdout: format!("ran: {cmd}"),
            stderr: String::new(),
            new_cwd: None,
        })
    });

    let spec = AgentSpec::new("ignored", 25).with_shell();
    let mut session =
        Session::open_seeded([7u8; 32], "dga1_renter_demo", spec).expect("open the hosted session");

    session.run_goal(
        "check out the repo and build it",
        &mut shell_plan(&["git clone …", "cargo build"]),
        &toolkit,
    );
    session.run_goal(
        "run the tests and summarize",
        &mut shell_plan(&["cargo test", "echo summary", "write report"]),
        &toolkit,
    );

    // ── the ARTIFACT: what the host hands back ────────────────────────────────
    let attestation = GrainAttestation::attest(&session);
    let bytes = serde_json::to_vec(&attestation).expect("serialize the artifact");
    println!("── grain attestation ──────────────────────────────────────────");
    println!("agent      : {}", attestation.agent());
    println!("signer     : {}", hex32(&attestation.signer()));
    println!(
        "chain tip  : {}",
        attestation
            .tip()
            .map(|t| hex32(&t))
            .unwrap_or_else(|| "<none>".into())
    );
    println!("artifact   : {} bytes (serde_json)", bytes.len());

    // ── the RENTER side: pin (signer, tip), re-witness, trust no host ─────────
    // The renter received the promised signer key out-of-band (the VK-anchor
    // analogue). It decodes the artifact and verifies against that pinned key.
    let promised_signer = attestation.signer();
    let received: GrainAttestation = serde_json::from_slice(&bytes).expect("decode the artifact");

    match received.verify_against_signer(&promised_signer) {
        Ok(v) => {
            println!("── renter verdict (R0 — tamper-evidence under the pinned signer) ──");
            println!("{}", v.summary());
            println!("  actions genuine + ordered : {}", v.actions);
            println!(
                "  consumed / budget         : {} / {}",
                v.consumed, v.budget
            );
            println!("  headroom (could-still-do) : {}", v.headroom);
            println!(
                "  bound airtight            : consumed + headroom == budget → {}",
                v.consumed + v.headroom == v.budget
            );
            println!("  ✓ this report was not mutated in transit: every receipt signed +");
            println!("    ordered under the pinned key, within budget at every step.");
            println!("  ⚠ NOT yet established here: completeness (\"nothing else\") and");
            println!("    host-independence — those are the higher rungs (R1 anchor, R2");
            println!("    kernel links, R3 STARK fold; see the honest boundary below).");
        }
        Err(e) => {
            eprintln!("renter REFUSED the attestation: {e}");
            std::process::exit(1);
        }
    }

    // ── the honest boundary ───────────────────────────────────────────────────
    println!("── honest boundary (whole-history light client) ───────────────");
    println!("{WHOLE_HISTORY_GAP}");

    std::fs::remove_dir_all(&dir).ok();
}

fn hex32(b: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for byte in b {
        s.push_str(&format!("{byte:02x}"));
    }
    s
}
