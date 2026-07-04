//! `gen-fixture` — emit sample `GrainAttestation` JSON for the browser page + the
//! headless agreement test. Drives a real hosted session (the HOST side), then
//! writes the artifacts a RENTER would paste into the page.
//!
//! Run: `cargo run -p grain-verify-wasm --bin gen-fixture -- <out-dir>`
//! (defaults to `web/fixtures/`). Writes:
//!   * `pass.json`        — a genuine attestation (base verify → PASS)
//!   * `tampered.json`    — the same chain with one action forged (verify → FAIL)
//!   * `renter.json`      — a genuine attestation WITH an R1 renter anchor
//!   * `pins.json`        — the out-of-band pins a renter types: signer, and for
//!                          renter.json the renter pubkey + genesis nonce.

use dregg_agent::agent::{AgentAction, AgentSpec, PlannedBrain, ToolCall};
use dregg_agent::session::Session;
use dregg_agent::toolkit::Toolkit;
use dregg_agent::tools::{OperatorTools, ShellOut};
use grain_verify::{GenesisPin, GrainAttestation, countersign_checkpoint};
use std::path::{Path, PathBuf};

fn shell_plan(cmds: &[&str]) -> PlannedBrain {
    PlannedBrain::new(
        cmds.iter()
            .map(|c| AgentAction::Op(ToolCall::new("shell", [("cmd".to_string(), c.to_string())])))
            .collect(),
    )
}

fn echo_toolkit(wd: &Path) -> OperatorTools {
    OperatorTools::new(Toolkit::new(), wd).with_shell(|cmd: &str, _cwd: &Path| {
        Ok(ShellOut {
            exit: 0,
            stdout: format!("ran: {cmd}"),
            stderr: String::new(),
            new_cwd: None,
        })
    })
}

fn hex32(b: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for byte in b {
        s.push_str(&format!("{byte:02x}"));
    }
    s
}

fn main() {
    let out_dir: PathBuf = std::env::args()
        .nth(1)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("web/fixtures"));
    std::fs::create_dir_all(&out_dir).expect("create out dir");

    let work = std::env::temp_dir().join(format!("gen-fixture-{}", std::process::id()));
    std::fs::create_dir_all(&work).unwrap();
    let tk = echo_toolkit(&work);

    // ── genuine session (base tamper-evidence) ────────────────────────────────
    let spec = AgentSpec::new("ignored", 25).with_shell();
    let mut sess = Session::open_seeded([7u8; 32], "dga1_renter_demo", spec).unwrap();
    sess.run_goal(
        "check out the repo and build it",
        &mut shell_plan(&["git clone …", "cargo build"]),
        &tk,
    );
    sess.run_goal(
        "run the tests and summarize",
        &mut shell_plan(&["cargo test", "echo summary", "write report"]),
        &tk,
    );

    let pass = GrainAttestation::attest(&sess);
    let signer = pass.signer();
    write_json(&out_dir.join("pass.json"), &pass);
    pass.verify()
        .expect("the genuine fixture verifies (sanity)");

    // ── tampered: forge one action (verify → FAIL) ────────────────────────────
    let mut tampered = pass.clone();
    tampered.report.receipts[0].action = "shell:forged-i-never-ran-this".into();
    write_json(&out_dir.join("tampered.json"), &tampered);
    assert!(
        tampered.verify().is_err(),
        "the tampered fixture fails (sanity)"
    );

    // ── renter-anchored (R1): countersign after goal one, keep running ─────────
    let renter_seed = [0x5au8; 32];
    let renter_nonce = [0x11u8; 32];
    let rspec = AgentSpec::new("ignored", 40).with_shell();
    let mut rsess = Session::open_seeded([21u8; 32], "dga1_renter_demo", rspec).unwrap();
    rsess.run_goal("goal one", &mut shell_plan(&["a", "b"]), &tk);
    let early = GrainAttestation::attest(&rsess);
    let cp = early
        .checkpoint_to_countersign()
        .expect("a 2-turn checkpoint to countersign");
    let cs = countersign_checkpoint(renter_seed, cp);
    let renter_pub = cs.renter_pubkey;
    rsess.run_goal("goal two", &mut shell_plan(&["c", "d", "e"]), &tk);
    let rsigner = GrainAttestation::attest(&rsess).signer();
    let renter_att = GrainAttestation::attest(&rsess)
        .with_genesis(GenesisPin {
            renter_nonce,
            signer: rsigner,
        })
        .with_checkpoint(cs);
    write_json(&out_dir.join("renter.json"), &renter_att);
    renter_att
        .verify_for_renter(&renter_pub, &renter_nonce)
        .expect("the renter fixture verifies (sanity)");

    // ── the out-of-band pins a renter types ───────────────────────────────────
    let pins = serde_json::json!({
        "pass_and_tampered_signer": hex32(&signer),
        "renter": {
            "signer": hex32(&rsigner),
            "renter_pubkey": hex32(&renter_pub),
            "genesis_nonce": hex32(&renter_nonce),
        }
    });
    std::fs::write(
        out_dir.join("pins.json"),
        serde_json::to_vec_pretty(&pins).unwrap(),
    )
    .unwrap();

    std::fs::remove_dir_all(&work).ok();

    eprintln!("wrote fixtures to {}", out_dir.display());
    eprintln!("  pass.json / tampered.json signer: {}", hex32(&signer));
    eprintln!(
        "  renter.json signer={} pubkey={} nonce={}",
        hex32(&rsigner),
        hex32(&renter_pub),
        hex32(&renter_nonce)
    );
}

fn write_json(path: &Path, att: &GrainAttestation) {
    let bytes = serde_json::to_vec_pretty(att).expect("serialize attestation");
    std::fs::write(path, bytes).expect("write fixture");
}
