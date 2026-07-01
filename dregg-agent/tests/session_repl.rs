//! End-to-end tests for the **hosted agent session** + the **SSH attach** — the
//! distribution model proven against the real `dregg-agent` binary, std-only
//! (recorded brain; no key, no network LLM, no real sshd).
//!
//! The proof the task asks for, locally simulated:
//!
//! 1. a user "ssh"es into a hosted session (we drive the same `attach` REPL the
//!    SSH forced-command drops into, over a piped stdin) → types a goal → it runs
//!    bounded + proven (cap-gated · metered · receipted);
//! 2. the budget draws down **across goals** (one ceiling for the whole session,
//!    no per-goal reset a runaway could exploit);
//! 3. a cap outside the bundle is **refused**;
//! 4. `verify` re-witnesses the whole session (host untrusted);
//! 5. a second account's session is **isolated** (its own budget + agent identity).

use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU32, Ordering};

fn bin() -> &'static str {
    env!("CARGO_BIN_EXE_dregg-agent")
}

/// A fresh unique temp dir (no `tempfile` dev-dep needed). Best-effort cleanup is
/// the OS temp sweep; tests do not collide (pid + a process-unique counter).
fn tmpdir() -> PathBuf {
    static N: AtomicU32 = AtomicU32::new(0);
    let p = std::env::temp_dir().join(format!(
        "dregg-session-e2e-{}-{}",
        std::process::id(),
        N.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&p).unwrap();
    p
}

/// Two recorded chat-completions responses: a `shell` tool-call, then `finish`.
/// `RecordedOpenAICaller::repeating` repeats `finish` once exhausted, so a fresh
/// brain per goal does exactly one admitted shell op then ends — deterministic.
const RECORDED_RESPONSES: &str = r#"[
  {"choices":[{"message":{"role":"assistant","tool_calls":[
    {"id":"c1","type":"function","function":{"name":"shell","arguments":"{\"cmd\":\"echo hello-from-agent\"}"}}
  ]}}]},
  {"choices":[{"message":{"role":"assistant","tool_calls":[
    {"id":"c2","type":"function","function":{"name":"finish","arguments":"{\"summary\":\"done\"}"}}
  ]}}]}
]"#;

/// Write the recorded responses to `dir/resp.json` and return its path string.
fn write_resp(dir: &std::path::Path) -> String {
    let p = dir.join("resp.json");
    std::fs::write(&p, RECORDED_RESPONSES).unwrap();
    p.to_string_lossy().into_owned()
}

/// A HOSTED-safe recorded brain: an `fs_write` (workdir-confined) tool-call then
/// `finish`. The hosted attach grants the lexically-confined tools (fs/http/…) but
/// NEVER a raw `shell` (the box holds the operator keys and the per-tenant OS jail
/// is not wired), so the SSH-attach proofs use `fs` — a real admitted, metered,
/// receipted action that does not need a shell.
const RECORDED_FS_RESPONSES: &str = r#"[
  {"choices":[{"message":{"role":"assistant","tool_calls":[
    {"id":"c1","type":"function","function":{"name":"fs_write","arguments":"{\"path\":\"note.txt\",\"content\":\"hello-from-agent\"}"}}
  ]}}]},
  {"choices":[{"message":{"role":"assistant","tool_calls":[
    {"id":"c2","type":"function","function":{"name":"finish","arguments":"{\"summary\":\"done\"}"}}
  ]}}]}
]"#;

/// Write the hosted-safe (fs) recorded responses to `dir/fs_resp.json`.
fn write_fs_resp(dir: &std::path::Path) -> String {
    let p = dir.join("fs_resp.json");
    std::fs::write(&p, RECORDED_FS_RESPONSES).unwrap();
    p.to_string_lossy().into_owned()
}

/// Run `dregg-agent <args...>` with `stdin_text` piped + `env` extras; return
/// (success, stdout ++ stderr). Refusals (`bad --caps: …`) print to stderr, so the
/// combined stream lets a test assert on either.
fn run(args: &[&str], stdin_text: &str, env: &[(&str, &str)]) -> (bool, String) {
    let mut cmd = Command::new(bin());
    cmd.args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut has_state_dir = false;
    for (k, v) in env {
        cmd.env(k, v);
        if *k == "DREGG_AGENT_STATE_DIR" {
            has_state_dir = true;
        }
    }
    // Isolate the durable per-account budget store to a fresh dir per call (unless a
    // test pins one, e.g. the persistence proof), so tests never pollute the real
    // ~/.dregg-agent/state and a re-run always starts from a clean drawdown.
    if !has_state_dir {
        cmd.env("DREGG_AGENT_STATE_DIR", tmpdir());
    }
    let mut child = cmd.spawn().expect("spawn dregg-agent");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(stdin_text.as_bytes())
        .unwrap();
    let out = child.wait_with_output().expect("wait dregg-agent");
    let mut combined = String::from_utf8_lossy(&out.stdout).into_owned();
    combined.push_str(&String::from_utf8_lossy(&out.stderr));
    (out.status.success(), combined)
}

// ── (1)+(2)+(4) the interactive session: budget draws down across goals; verify ──

#[test]
fn a_session_runs_goals_draws_budget_down_across_them_and_verifies() {
    let dir = tmpdir();
    let resp = write_resp(dir.as_path());
    let out_file = dir.as_path().join("session.json");

    // Drive the REPL: two goals, then :verify, then :quit.
    let stdin = "clone and inspect a repo\nnow summarize what you found\n:verify\n:quit\n";
    let (ok, out) = run(
        &[
            "session",
            "--account",
            "dga1_demo",
            "--budget",
            "10",
            "--caps",
            "shell",
            "--replay",
            &resp,
            "--out",
            out_file.to_str().unwrap(),
        ],
        stdin,
        &[],
    );
    assert!(ok, "session exited non-zero:\n{out}");

    // Each goal ran one admitted shell op, narrated as a receipted step.
    assert!(out.contains("step  1"), "no narrated step:\n{out}");
    assert!(out.contains("admitted"), "no admitted action:\n{out}");

    // THE BUDGET DRAWS DOWN ACROSS GOALS: goal 1 → 1¢, goal 2 → 2¢ (no reset).
    assert!(
        out.contains("consumed 1¢ / 10¢"),
        "goal 1 should consume 1¢:\n{out}"
    );
    assert!(
        out.contains("consumed 2¢ / 10¢"),
        "goal 2 should consume 2¢ cumulatively:\n{out}"
    );

    // :verify re-witnessed the WHOLE session (both goals in one chain).
    assert!(
        out.contains("the WHOLE session re-witnesses: 2 signed action(s)"),
        "session verify missing/ wrong count:\n{out}"
    );

    // The artifact was written and re-witnesses offline via the existing verifier.
    assert!(out_file.exists(), "no session.json written:\n{out}");
    let (vok, vout) = run(&["verify", out_file.to_str().unwrap()], "", &[]);
    assert!(vok, "verify of the session artifact failed:\n{vout}");
    assert!(
        vout.contains("re-verifies"),
        "verify verdict missing:\n{vout}"
    );
}

// ── (1) the SSH attach: a forced-command drop-in, scoped to ONE account ──────────

#[test]
fn ssh_attach_one_shot_runs_the_goal_scoped_to_the_account() {
    let dir = tmpdir();
    let resp = write_fs_resp(dir.as_path());

    // `ssh dga1_alice@host "do a thing"` → the forced command runs `attach`, the
    // goal arrives as SSH_ORIGINAL_COMMAND, runs once, prints the proof, exits.
    // The hosted attach grants the lexically-confined tools (fs/http/…), NEVER a raw
    // `shell` (the box holds the operator keys), so the goal does an `fs` write.
    let (ok, out) = run(
        &[
            "attach",
            "--account",
            "dga1_alice",
            "--budget",
            "5",
            "--caps",
            "fs",
            "--replay",
            &resp,
        ],
        "", // no interactive stdin — the one-shot path
        &[("SSH_ORIGINAL_COMMAND", "do a single thing")],
    );
    assert!(ok, "attach exited non-zero:\n{out}");
    assert!(out.contains("ATTACHED"), "no attach banner:\n{out}");
    assert!(
        out.contains("dga1_alice") && out.contains("agent:session:dga1_alice"),
        "session not scoped to the account:\n{out}"
    );
    assert!(out.contains("admitted"), "the goal did not run:\n{out}");
    assert!(
        out.contains("the WHOLE session re-witnesses: 1 signed action(s)"),
        "attach session did not verify:\n{out}"
    );
}

// ── (2) THE CRITICAL: a HOSTED attach ALWAYS refuses the `shell` cap ──────────

#[test]
fn hosted_attach_refuses_the_shell_cap() {
    let dir = tmpdir();
    let resp = write_resp(dir.as_path());

    // `attach` is the hosted SSH drop-in. A `shell` cap would let a tenant read the
    // operator's keys — so it is REFUSED at parse, fail-closed, before any session
    // opens. This is the red-team CRITICAL, closed.
    let (ok, out) = run(
        &[
            "attach",
            "--account",
            "dga1_evil",
            "--budget",
            "5",
            "--caps",
            "shell,fs",
            "--replay",
            &resp,
        ],
        "",
        &[("SSH_ORIGINAL_COMMAND", "cat /home/op/.stripekey")],
    );
    assert!(!ok, "a hosted shell grant must exit non-zero:\n{out}");
    assert!(
        out.contains("shell") && out.contains("hosted"),
        "the refusal must name the shell cap + hosted posture:\n{out}"
    );
    // No session banner: it never opened (refused before open).
    assert!(
        !out.contains("ATTACHED"),
        "no session should have opened:\n{out}"
    );
}

// ── (F1) the decorative `--os-isolation` flag is REFUSED — never grants a shell ──

#[test]
fn os_isolation_flag_is_refused_and_never_grants_a_shell() {
    let dir = tmpdir();
    let resp = write_resp(dir.as_path());

    // `--os-isolation` used to flip a hosted session back to the local posture and
    // re-grant a raw `shell` on the operator-key-holding host — but the per-tenant
    // jail it named ran NOWHERE. It is now a hard error: the session refuses to
    // start rather than hand out an unconfined shell behind a decorative flag.
    let (ok, out) = run(
        &[
            "attach",
            "--account",
            "dga1_evil",
            "--budget",
            "5",
            "--os-isolation",
            "--caps",
            "shell",
            "--replay",
            &resp,
        ],
        "",
        &[("SSH_ORIGINAL_COMMAND", "cat /home/op/.stripekey")],
    );
    assert!(
        !ok,
        "--os-isolation must exit non-zero (no fake jail):\n{out}"
    );
    assert!(
        out.contains("os-isolation") && out.contains("not available"),
        "the refusal must name the unavailable isolation flag:\n{out}"
    );
    // No session opened → no shell ran → the operator key was never reachable.
    assert!(
        !out.contains("ATTACHED") && !out.contains("admitted"),
        "no session/shell should have run behind the flag:\n{out}"
    );
}

// ── (F1) the LOCAL own-box shell path is UNAFFECTED ──────────────────────────

#[test]
fn a_local_session_still_grants_a_shell() {
    let dir = tmpdir();
    let resp = write_resp(dir.as_path());

    // `session` (not `attach`) is the user's OWN box: a raw `shell` remains theirs
    // to grant — the F1 fix only closes the HOSTED path, never the local one.
    let (ok, out) = run(
        &[
            "session",
            "--account",
            "dga1_me",
            "--budget",
            "5",
            "--caps",
            "shell",
            "--replay",
            &resp,
        ],
        "run a command\n:quit\n",
        &[],
    );
    assert!(ok, "a local shell session must run:\n{out}");
    assert!(
        out.contains("CONFINE local") && out.contains("admitted"),
        "the local shell op should run admitted:\n{out}"
    );
}

// ── (3) the cap-scoping tooth: an out-of-bundle tool is refused in the REPL ──────

#[test]
fn an_out_of_bundle_tool_is_refused_in_the_session() {
    let dir = tmpdir();
    let resp = write_resp(dir.as_path());

    // The bundle grants `fs` but NOT `shell`; the recorded brain calls `shell`.
    let stdin = "try to run a shell command\n:quit\n";
    let (ok, out) = run(
        &[
            "session",
            "--account",
            "dga1_locked",
            "--budget",
            "10",
            "--caps",
            "fs",
            "--replay",
            &resp,
        ],
        stdin,
        &[],
    );
    assert!(ok, "session exited non-zero:\n{out}");
    assert!(
        out.contains("cap-refused") && out.contains("outside the cap bundle"),
        "the out-of-bundle shell was not refused:\n{out}"
    );
    // No money/effect, but the session still re-witnesses (a refusal leaves no receipt).
    assert!(
        out.contains("0 signed action(s)") || out.contains("re-witnesses"),
        "session should still verify after a refusal:\n{out}"
    );
}

// ── (5) multi-user isolation: each account its own budget + identity ─────────────

#[test]
fn two_accounts_are_isolated_by_their_own_budget_and_identity() {
    let dir = tmpdir();
    let resp = write_fs_resp(dir.as_path());

    // Alice has a 1¢ ceiling → one hosted `fs` op exhausts her.
    let (aok, aout) = run(
        &[
            "attach",
            "--account",
            "dga1_alice",
            "--budget",
            "1",
            "--caps",
            "fs",
            "--replay",
            &resp,
        ],
        "",
        &[("SSH_ORIGINAL_COMMAND", "work")],
    );
    assert!(aok);
    assert!(
        aout.contains("consumed 1¢ / 1¢") && aout.contains("headroom 0¢"),
        "alice not bounded by her own ceiling:\n{aout}"
    );
    assert!(aout.contains("agent:session:dga1_alice"));

    // Bob has a 100¢ ceiling → the same op leaves him almost full. His budget and
    // identity are entirely his own — alice's exhaustion does not touch him.
    let (bok, bout) = run(
        &[
            "attach",
            "--account",
            "dga1_bob",
            "--budget",
            "100",
            "--caps",
            "fs",
            "--replay",
            &resp,
        ],
        "",
        &[("SSH_ORIGINAL_COMMAND", "work")],
    );
    assert!(bok);
    assert!(
        bout.contains("consumed 1¢ / 100¢") && bout.contains("headroom 99¢"),
        "bob's budget is not his own:\n{bout}"
    );
    assert!(bout.contains("agent:session:dga1_bob"));
}

// ── (F2) the budget PERSISTS across attach PROCESSES (SSH detach/re-attach) ──────

#[test]
fn the_budget_persists_across_attach_processes_and_over_budget_is_refused() {
    let dir = tmpdir();
    let resp = write_fs_resp(dir.as_path());
    // A SHARED durable store across the three "SSH connections" (distinct processes),
    // keyed by account under this stable dir — the twin of a real per-host volume.
    let state = dir.join("shared-state");
    let state_s = state.to_str().unwrap();
    let env = |extra: &'static str| {
        vec![
            ("SSH_ORIGINAL_COMMAND", extra),
            ("DREGG_AGENT_STATE_DIR", state_s),
        ]
    };
    let attach = |e: Vec<(&str, &str)>| {
        run(
            &[
                "attach",
                "--account",
                "dga1_recon",
                "--budget",
                "2",
                "--caps",
                "fs",
                "--replay",
                &resp,
            ],
            "",
            &e,
        )
    };

    // Connection 1: one fs op draws 1¢ of the 2¢ ceiling; the drawdown is persisted.
    let (ok1, out1) = attach(env("work"));
    assert!(ok1, "attach 1 failed:\n{out1}");
    assert!(
        out1.contains("consumed 1¢ / 2¢"),
        "attach 1 should draw 1¢:\n{out1}"
    );

    // Connection 2 (a FRESH process → fresh in-memory meter): the ceiling is still
    // DRAWN DOWN (not reset to full), so the second op consumes the LAST 1¢.
    let (ok2, out2) = attach(env("work again"));
    assert!(ok2, "attach 2 failed:\n{out2}");
    assert!(
        out2.contains("consumed 2¢ / 2¢") && out2.contains("headroom 0¢"),
        "the budget RESET on re-attach (F2 hole) instead of persisting:\n{out2}"
    );

    // Connection 3: over budget ACROSS the reconnect → the op is refused in-band,
    // nothing admitted. A tenant cannot get the full budget again by reconnecting.
    let (ok3, out3) = attach(env("try to overspend"));
    assert!(ok3, "attach 3 failed:\n{out3}");
    assert!(
        out3.contains("0 admitted") && out3.contains("budget-refused"),
        "over-budget was NOT refused across the reconnect:\n{out3}"
    );
}
