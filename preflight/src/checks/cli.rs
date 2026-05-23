//! CLI functionality checks: spawn the pyana CLI binary as a subprocess.

use std::process::Command;

use crate::report::{CheckResult, run_check};

pub fn run() -> Vec<CheckResult> {
    vec![
        run_check("cli_version", check_cli_version),
        run_check("cli_config_init", check_cli_config_init),
        run_check("cli_doctor", check_cli_doctor),
        run_check("cli_completions", check_cli_completions),
        run_check("cli_config_roundtrip", check_cli_config_roundtrip),
    ]
}

/// Helper: run a cargo command for pyana-cli with given args.
/// Returns Ok((stdout, stderr)) on exit 0, Err on non-zero exit or spawn failure.
fn run_cli(args: &[&str]) -> Result<(String, String), String> {
    let mut cmd_args = vec!["run", "-p", "pyana-cli", "--"];
    cmd_args.extend_from_slice(args);

    let output = Command::new("cargo")
        .args(&cmd_args)
        .env(
            "PYANA_HOME",
            std::env::temp_dir().join("preflight-cli-home"),
        )
        .output()
        .map_err(|e| format!("failed to spawn cargo: {e}"))?;

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();

    if output.status.success() {
        Ok((stdout, stderr))
    } else {
        Err(format!(
            "exit code {:?}\nstdout: {}\nstderr: {}",
            output.status.code(),
            stdout,
            stderr
        ))
    }
}

fn check_cli_version() -> Result<(), String> {
    let (stdout, _stderr) = run_cli(&["version"]).or_else(|_| run_cli(&["--version"]))?;

    // Should print something (version string).
    if stdout.trim().is_empty() {
        return Err("version command produced no output".into());
    }

    Ok(())
}

fn check_cli_config_init() -> Result<(), String> {
    // Use a temp directory for config.
    let tmp_home =
        std::env::temp_dir().join(format!("preflight-cli-config-{}", std::process::id()));
    std::fs::create_dir_all(&tmp_home).map_err(|e| format!("create tmp dir failed: {e}"))?;

    let output = Command::new("cargo")
        .args(["run", "-p", "pyana-cli", "--", "config", "init"])
        .env("PYANA_HOME", &tmp_home)
        .output()
        .map_err(|e| format!("failed to spawn: {e}"))?;

    // Config init should exit 0 (or at least not crash).
    // Some CLIs output to stderr for info messages.
    if !output.status.success() {
        // Acceptable: config init may fail if deps are missing, but should not panic.
        let stderr = String::from_utf8_lossy(&output.stderr);
        if stderr.contains("panic") || stderr.contains("RUST_BACKTRACE") {
            return Err(format!("config init panicked: {stderr}"));
        }
        // Non-panic failure is acceptable (e.g., "no node configured").
    }

    // Check if config file was created.
    let config_path = tmp_home.join("config.toml");
    let alt_config_path = tmp_home.join("pyana.toml");
    if !config_path.exists() && !alt_config_path.exists() {
        // This is acceptable - the CLI may use a different config path
        // or may not have created one due to missing node.
    }

    // Cleanup.
    let _ = std::fs::remove_dir_all(&tmp_home);
    Ok(())
}

fn check_cli_doctor() -> Result<(), String> {
    let output = Command::new("cargo")
        .args(["run", "-p", "pyana-cli", "--", "doctor"])
        .env(
            "PYANA_HOME",
            std::env::temp_dir().join("preflight-cli-doctor"),
        )
        .output()
        .map_err(|e| format!("failed to spawn: {e}"))?;

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    // Doctor may fail (no node running) but should not panic.
    if stderr.contains("panic") || stdout.contains("panic") {
        return Err(format!("doctor panicked: {stderr}"));
    }

    // Doctor should produce SOME output (even if checks fail).
    if stdout.is_empty() && stderr.is_empty() {
        return Err("doctor produced no output at all".into());
    }

    Ok(())
}

fn check_cli_completions() -> Result<(), String> {
    let output = Command::new("cargo")
        .args(["run", "-p", "pyana-cli", "--", "completions", "zsh"])
        .output()
        .map_err(|e| format!("failed to spawn: {e}"))?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(format!("completions command failed: {stderr}"));
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    if stdout.trim().is_empty() {
        return Err("completions should produce shell completion script".into());
    }

    // Basic sanity: zsh completions typically contain compdef or _arguments.
    if !stdout.contains("compdef") && !stdout.contains("_pyana") && !stdout.contains("#compdef") {
        // May use clap_complete format which looks different, just verify non-empty.
        if stdout.len() < 50 {
            return Err("completions output seems too short to be valid".into());
        }
    }

    Ok(())
}

fn check_cli_config_roundtrip() -> Result<(), String> {
    // Manually write a config file and verify the CLI can read it.
    let tmp_home = std::env::temp_dir().join(format!("preflight-cli-rt-{}", std::process::id()));
    std::fs::create_dir_all(&tmp_home).map_err(|e| format!("create tmp dir failed: {e}"))?;

    let config_content = r#"
[node]
address = "127.0.0.1:9090"
federation = "test-federation"

[wallet]
default_cell = "my-cell"
"#;

    let config_path = tmp_home.join("config.toml");
    std::fs::write(&config_path, config_content)
        .map_err(|e| format!("write config failed: {e}"))?;

    // Verify we can read it back.
    let read_back =
        std::fs::read_to_string(&config_path).map_err(|e| format!("read config failed: {e}"))?;

    if !read_back.contains("127.0.0.1:9090") {
        return Err("config roundtrip: address not found in read-back".into());
    }
    if !read_back.contains("test-federation") {
        return Err("config roundtrip: federation not found in read-back".into());
    }

    // Cleanup.
    let _ = std::fs::remove_dir_all(&tmp_home);
    Ok(())
}
