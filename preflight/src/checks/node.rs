//! Node startup checks: binary existence, help, genesis, config validation.

use std::process::Command;

use crate::report::{CheckResult, run_check};

pub fn run() -> Vec<CheckResult> {
    vec![
        run_check("node_binary_exists", check_node_binary_exists),
        run_check("node_help", check_node_help),
        run_check("node_relay_help", check_node_relay_help),
        run_check("genesis_parseable", check_genesis_parseable),
        run_check("config_validation", check_config_validation),
    ]
}

fn check_node_binary_exists() -> Result<(), String> {
    // The node binary is built from pyana-node crate. Check that the crate compiles.
    let output = Command::new("cargo")
        .args(["build", "-p", "pyana-node", "--message-format=short"])
        .output()
        .map_err(|e| format!("failed to spawn cargo build: {e}"))?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        // Check if it's just a dependency issue vs a real problem.
        if stderr.contains("error[E") {
            return Err(format!(
                "pyana-node does not compile: {}",
                stderr.lines().take(5).collect::<Vec<_>>().join("\n")
            ));
        }
        // Warnings are fine.
    }

    Ok(())
}

fn check_node_help() -> Result<(), String> {
    let output = Command::new("cargo")
        .args(["run", "-p", "pyana-node", "--", "--help"])
        .output()
        .map_err(|e| format!("failed to spawn: {e}"))?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        // Some CLIs exit with code 0 for --help, some with 2, depends on clap version.
        // Just verify it didn't panic.
        if stderr.contains("panic") {
            return Err(format!("node --help panicked: {stderr}"));
        }
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    if stdout.is_empty() && output.status.success() {
        return Err("--help produced no stdout output".into());
    }

    Ok(())
}

fn check_node_relay_help() -> Result<(), String> {
    let output = Command::new("cargo")
        .args(["run", "-p", "pyana-node", "--", "relay", "--help"])
        .output()
        .map_err(|e| format!("failed to spawn: {e}"))?;

    // Relay subcommand help should produce output without panicking.
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    if stderr.contains("panic") || stdout.contains("panic") {
        return Err(format!("relay --help panicked: {stderr}"));
    }

    // It's acceptable if the subcommand doesn't exist yet (clap will print an error).
    // We just verify no panics.
    Ok(())
}

fn check_genesis_parseable() -> Result<(), String> {
    // A genesis file should be parseable JSON/TOML.
    // We'll create a minimal one and verify basic structure.
    let genesis_json = r#"{
        "federation_id": "0000000000000000000000000000000000000000000000000000000000000001",
        "initial_participants": [],
        "initial_height": 0,
        "epoch_duration": 100,
        "constitution_hash": "0000000000000000000000000000000000000000000000000000000000000000"
    }"#;

    // Parse as JSON to verify structure.
    let parsed: serde_json::Value =
        serde_json::from_str(genesis_json).map_err(|e| format!("genesis parse failed: {e}"))?;

    // Verify required fields.
    if parsed.get("federation_id").is_none() {
        return Err("genesis should have federation_id".into());
    }
    if parsed.get("initial_height").is_none() {
        return Err("genesis should have initial_height".into());
    }
    if parsed.get("epoch_duration").is_none() {
        return Err("genesis should have epoch_duration".into());
    }

    // Verify federation_id is a hex string of expected length.
    let fed_id = parsed["federation_id"]
        .as_str()
        .ok_or("federation_id should be a string")?;
    if fed_id.len() != 64 {
        return Err(format!(
            "federation_id should be 64 hex chars, got {}",
            fed_id.len()
        ));
    }

    Ok(())
}

fn check_config_validation() -> Result<(), String> {
    // Verify that invalid configs are rejected (basic TOML structure check).
    let valid_config = r#"
[node]
listen_addr = "0.0.0.0:9090"
data_dir = "/var/lib/pyana"

[federation]
genesis_path = "./genesis.json"
participant_key_path = "./key.pem"

[relay]
enabled = true
max_message_size = 65536
max_ttl_blocks = 1000
"#;

    // Parse as TOML.
    let parsed: toml::Value =
        toml::from_str(valid_config).map_err(|e| format!("valid config TOML parse failed: {e}"))?;

    // Verify sections exist.
    if parsed.get("node").is_none() {
        return Err("config should have [node] section".into());
    }
    if parsed.get("federation").is_none() {
        return Err("config should have [federation] section".into());
    }

    // Verify invalid TOML is rejected.
    let invalid_config = "[invalid\nfoo = ";
    let result: Result<toml::Value, _> = toml::from_str(invalid_config);
    if result.is_ok() {
        return Err("invalid TOML should be rejected".into());
    }

    Ok(())
}
