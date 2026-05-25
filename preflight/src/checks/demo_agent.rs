//! Demo-agent example runner: exercises every binary under demo-agent/examples/.
//!
//! Each example is compiled and run via `cargo run --example <name> -p pyana-demo-agent`.
//! The check reports PASS or FAIL with a human-readable reason for each example, then
//! returns aggregate success only if ALL examples pass.
//!
//! Failure categories:
//!   - COMPILE ERROR  — `cargo` exits non-zero before the binary starts (error[E…] in stderr)
//!   - RUNTIME ERROR  — binary starts but exits non-zero (panic / assertion / explicit exit)
//!   - TIMEOUT        — example did not complete within the per-example deadline
//!   - INFRA SKIP     — example detects missing infrastructure and explicitly requests a skip
//!     (detected via special output markers, see [`SKIP_MARKERS`])
//!
//! Timeout is 60 s per example, enforced via a background thread so a hung example
//! does not block the whole preflight.

use std::io::Read;
use std::process::{Child, Command, Stdio};
use std::sync::mpsc;
use std::time::Duration;

use crate::report::{CheckResult, run_check};

/// Per-example timeout.  Generous enough to cover release-mode compilation of
/// cryptographic examples; tight enough that a hung example doesn't block the run.
const EXAMPLE_TIMEOUT: Duration = Duration::from_secs(60);

/// If any of these strings appear in an example's stdout or stderr the example is
/// considered infrastructure-dependent and is reported as SKIP (not FAIL).
/// Examples must print one of these markers when they detect missing infrastructure.
const SKIP_MARKERS: &[&str] = &[
    "SKIP: node not running",
    "SKIP: missing env",
    "SKIP: no network",
    "PYANA_SKIP",
];

/// The full, ordered list of demo-agent examples.
/// This is intentionally hard-coded so the preflight is deterministic and so that
/// newly added examples must be explicitly registered here (i.e., registration is a
/// conscious act, not silent auto-discovery).
///
/// All 43 examples that exist under demo-agent/examples/ as of 2026-05-23.
const EXAMPLES: &[&str] = &[
    "agent_network",
    "ai_agent_mcp_workflow",
    "anonymous_credit_check",
    "atomic_swap_demo",
    "auction_demo",
    "base_anonymous_credential",
    "base_private_transfer",
    "bench_summary",
    "causal_ordering",
    "cdt_revocation",
    "compute_marketplace",
    "cross_fed_atomic",
    "cross_federation_nft_swap",
    "delegation_demo",
    "delegation_swarm",
    "escrow_demo",
    "federation_bootstrap",
    "federation_exit",
    "intent_lifecycle",
    "ivc_attenuation_chain",
    "multi_org_delegation",
    "multi_silo_budget",
    "nft_demo",
    "note_bridge",
    "note_privacy",
    "offline_verification",
    "payment_channel",
    "payment_channel_burst",
    "pipeline_demo",
    "private_auction",
    "private_hiring",
    "private_orderbook",
    "programmable_cell",
    "progressive_disclosure",
    "proof_obligation",
    "rbac_datalog",
    "seal_unseal_transfer",
    "sub_agent_spawn",
    "three_party_introduction",
    "token_revocation",
    "unified_harness",
    "cipherclerk_lifecycle",
    "web_auth_flow",
];

pub fn run() -> Vec<CheckResult> {
    EXAMPLES
        .iter()
        .map(|name| run_check(name, || run_example(name)))
        .collect()
}

/// Run a single demo-agent example with a timeout.
///
/// Returns:
/// - `Ok(())` on exit-code 0
/// - `Err(reason)` on compile error, runtime error, or timeout
fn run_example(name: &str) -> Result<(), String> {
    // Spawn the child process.
    let mut child = Command::new("cargo")
        .args([
            "run",
            "--example",
            name,
            "-p",
            "pyana-demo-agent",
            "--message-format=short",
        ])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("failed to spawn cargo: {e}"))?;

    // Use a channel + thread to implement the timeout without external crates.
    // The thread calls wait() (blocking) and sends the result.
    // The main thread selects on the channel with a timeout.
    let (tx, rx) = mpsc::channel::<Result<std::process::Output, String>>();

    // We need to move the child's stdio handles into the thread.
    // Take them out of the child before handing the child to the thread.
    let mut stdout_pipe = child.stdout.take().unwrap();
    let mut stderr_pipe = child.stderr.take().unwrap();

    std::thread::spawn(move || {
        // Collect stdout/stderr while waiting (prevents pipe-full deadlock).
        let mut stdout_buf = Vec::new();
        let mut stderr_buf = Vec::new();

        // Read both pipes concurrently using two nested threads.
        let (so_tx, so_rx) = mpsc::channel::<Vec<u8>>();
        let (se_tx, se_rx) = mpsc::channel::<Vec<u8>>();

        std::thread::spawn(move || {
            let mut buf = Vec::new();
            let _ = stdout_pipe.read_to_end(&mut buf);
            let _ = so_tx.send(buf);
        });
        std::thread::spawn(move || {
            let mut buf = Vec::new();
            let _ = stderr_pipe.read_to_end(&mut buf);
            let _ = se_tx.send(buf);
        });

        let status = match child.wait() {
            Ok(s) => s,
            Err(e) => {
                let _ = tx.send(Err(format!("wait() failed: {e}")));
                return;
            }
        };

        stdout_buf = so_rx.recv().unwrap_or_default();
        stderr_buf = se_rx.recv().unwrap_or_default();

        let output = std::process::Output {
            status,
            stdout: stdout_buf,
            stderr: stderr_buf,
        };
        let _ = tx.send(Ok(output));
    });

    // Wait up to EXAMPLE_TIMEOUT for the child to finish.
    match rx.recv_timeout(EXAMPLE_TIMEOUT) {
        Ok(Ok(output)) => classify_output(name, output),
        Ok(Err(e)) => Err(e),
        Err(mpsc::RecvTimeoutError::Timeout) => {
            // The child is still running.  We cannot easily kill it here (the Child
            // was moved into the thread), but the preflight process will exit when
            // main() returns and the OS will reap the orphan.
            Err(format!(
                "TIMEOUT: example did not finish within {}s",
                EXAMPLE_TIMEOUT.as_secs()
            ))
        }
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            Err("TIMEOUT: worker thread panicked before sending result".into())
        }
    }
}

/// Classify an example's `Output` into Ok / Err with a meaningful reason.
fn classify_output(name: &str, output: std::process::Output) -> Result<(), String> {
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    // Check for infrastructure-skip markers first (regardless of exit code).
    for marker in SKIP_MARKERS {
        if stdout.contains(marker) || stderr.contains(marker) {
            return Err(format!(
                "INFRA SKIP: example requested skip (marker: {marker})"
            ));
        }
    }

    if output.status.success() {
        return Ok(());
    }

    // Failure: categorise the reason.
    let reason = categorise_failure(name, &stdout, &stderr, output.status.code());
    Err(reason)
}

/// Produce a human-readable failure reason from cargo/compiler output.
fn categorise_failure(_name: &str, stdout: &str, stderr: &str, exit_code: Option<i32>) -> String {
    // Cargo compile errors look like "error[E…]" in stderr.
    if stderr.contains("error[E") || stderr.contains("aborting due to") {
        let first_error = stderr
            .lines()
            .find(|l| l.contains("error[E") || l.starts_with("error:"))
            .unwrap_or("(see above)");
        return format!(
            "COMPILE ERROR: {} (exit {})",
            first_error.trim(),
            exit_code.map(|c| c.to_string()).unwrap_or("?".into())
        );
    }

    // Cargo "could not compile" without error[E] codes (e.g., link errors).
    if stderr.contains("could not compile") {
        let detail = stderr
            .lines()
            .find(|l| l.contains("error") && !l.contains("warning"))
            .unwrap_or("(see above)");
        return format!(
            "COMPILE ERROR (link/other): {} (exit {})",
            detail.trim(),
            exit_code.map(|c| c.to_string()).unwrap_or("?".into())
        );
    }

    // Runtime panics look like "thread 'main' panicked" in stderr.
    if stderr.contains("thread 'main' panicked") || stderr.contains("thread \"main\" panicked") {
        let panic_msg = stderr
            .lines()
            .find(|l| l.contains("panicked"))
            .unwrap_or("(panic, no message)");
        return format!(
            "RUNTIME PANIC: {} (exit {})",
            panic_msg.trim(),
            exit_code.map(|c| c.to_string()).unwrap_or("?".into())
        );
    }

    // Assertion failures (Rust's assert! / assert_eq!) look like "assertion failed".
    if stderr.contains("assertion") || stdout.contains("assertion") {
        let assert_msg = stderr
            .lines()
            .chain(stdout.lines())
            .find(|l| l.contains("assertion"))
            .unwrap_or("(assertion failed, no message)");
        return format!(
            "RUNTIME ASSERTION: {} (exit {})",
            assert_msg.trim(),
            exit_code.map(|c| c.to_string()).unwrap_or("?".into())
        );
    }

    // Generic failure.
    let stderr_tail: String = stderr
        .lines()
        .rev()
        .take(3)
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
        .collect::<Vec<_>>()
        .join(" | ");

    format!(
        "RUNTIME ERROR: exit {} | last stderr: {}",
        exit_code.map(|c| c.to_string()).unwrap_or("?".into()),
        if stderr_tail.is_empty() {
            "(no stderr)"
        } else {
            &stderr_tail
        }
    )
}
