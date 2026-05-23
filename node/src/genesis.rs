//! Genesis configuration generator for devnet federation setup.
//!
//! Generates:
//! - `genesis.json` — initial federation state
//! - `devnet-node-N.key` — per-node signing keys (hex-encoded, devnet-prefixed)
//! - `node-N.env` — per-node environment variable files
//! - `.devnet` — marker file indicating devnet data directory

use std::path::Path;

use serde::Serialize;

/// A validator entry in the genesis configuration.
#[derive(Serialize)]
struct GenesisValidator {
    name: String,
    public_key: String,
    xmss_root: String,
}

/// An initial cell in the genesis configuration.
#[derive(Serialize)]
struct GenesisCell {
    id: String,
    balance: u64,
}

/// The complete genesis configuration.
#[derive(Serialize)]
struct GenesisConfig {
    federation_id: String,
    epoch_length: u64,
    checkpoint_interval: u64,
    validators: Vec<GenesisValidator>,
    threshold: usize,
    initial_cells: Vec<GenesisCell>,
}

/// Run the genesis configuration generation.
pub fn run_genesis(validators: usize, epoch_length: u64, checkpoint_interval: u64, output: &Path) {
    if validators == 0 {
        eprintln!("error: must have at least 1 validator");
        std::process::exit(1);
    }

    // Create output directory.
    std::fs::create_dir_all(output).unwrap_or_else(|e| {
        eprintln!("error: failed to create output directory: {e}");
        std::process::exit(1);
    });

    // Generate a unique federation ID.
    let mut federation_id_bytes = [0u8; 16];
    getrandom::fill(&mut federation_id_bytes).expect("getrandom failed");
    let federation_id = hex_encode(&federation_id_bytes);

    // Generate keypairs for each validator.
    let mut genesis_validators = Vec::with_capacity(validators);

    for i in 0..validators {
        // Generate a 32-byte signing key.
        let mut key_bytes = [0u8; 32];
        getrandom::fill(&mut key_bytes).expect("getrandom failed");

        // Derive the Ed25519 public key.
        let signing_key = ed25519_dalek::SigningKey::from_bytes(&key_bytes);
        let public_key = signing_key.verifying_key();
        let pk_hex = hex_encode(public_key.as_bytes());

        // WARNING: This XMSS root is a placeholder for devnet. In production,
        // a real XMSS tree must be generated. See circuit/src/xmss.rs.
        eprintln!(
            "warning: generating placeholder XMSS root for node-{i} (not post-quantum secure)"
        );
        let xmss_root = blake3::derive_key("pyana-devnet-xmss-root-v1", &key_bytes);
        let xmss_root_hex = hex_encode(&xmss_root);

        genesis_validators.push(GenesisValidator {
            name: format!("node-{i}"),
            public_key: pk_hex,
            xmss_root: xmss_root_hex,
        });

        // Write the key file as raw 32 bytes (matching what the runtime expects).
        let key_path = output.join(format!("node-{i}.key"));
        std::fs::write(&key_path, &key_bytes).unwrap_or_else(|e| {
            eprintln!("error: failed to write {}: {e}", key_path.display());
            std::process::exit(1);
        });
        // Issue 6: Restrict key file permissions to owner-only (0o600).
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            std::fs::set_permissions(&key_path, std::fs::Permissions::from_mode(0o600))
                .unwrap_or_else(|e| {
                    eprintln!(
                        "error: failed to set permissions on {}: {e}",
                        key_path.display()
                    );
                    std::process::exit(1);
                });
        }

        // Write the env file.
        let env_path = output.join(format!("node-{i}.env"));
        let peers: Vec<String> = (0..validators)
            .filter(|&j| j != i)
            .map(|j| format!("node-{j}:9420"))
            .collect();
        let env_content = format!(
            "RUST_LOG=info\n\
             PYANA_NODE_INDEX={i}\n\
             PYANA_FEDERATION_SIZE={validators}\n\
             PYANA_FEDERATION_PEERS={peers}\n\
             PYANA_DATA_DIR=/data\n\
             PYANA_PORT=8420\n\
             PYANA_GOSSIP_PORT=9420\n",
            peers = peers.join(","),
        );
        std::fs::write(&env_path, &env_content).unwrap_or_else(|e| {
            eprintln!("error: failed to write {}: {e}", env_path.display());
            std::process::exit(1);
        });
    }

    // BFT quorum threshold: n - floor((n-1)/3) for n validators.
    let threshold = pyana_federation::quorum_threshold(validators);

    // Build genesis config.
    let genesis = GenesisConfig {
        federation_id,
        epoch_length,
        checkpoint_interval,
        validators: genesis_validators,
        threshold,
        initial_cells: vec![
            GenesisCell {
                id: "treasury".to_string(),
                balance: 1_000_000,
            },
            GenesisCell {
                id: "faucet".to_string(),
                balance: 100_000,
            },
        ],
    };

    // Write genesis.json.
    let genesis_path = output.join("genesis.json");
    let genesis_json = serde_json::to_string_pretty(&genesis).expect("failed to serialize genesis");
    std::fs::write(&genesis_path, &genesis_json).unwrap_or_else(|e| {
        eprintln!("error: failed to write genesis.json: {e}");
        std::process::exit(1);
    });

    // Write `.devnet` marker so the runtime can detect devnet data directories.
    let devnet_marker_path = output.join(".devnet");
    std::fs::write(
        &devnet_marker_path,
        "# This directory contains devnet configuration.\n# Keys here are NOT production-grade.\n",
    )
    .unwrap_or_else(|e| {
        eprintln!("error: failed to write .devnet marker: {e}");
        std::process::exit(1);
    });

    println!(
        "Devnet genesis configuration generated in {}",
        output.display()
    );
    println!("  Federation ID: {}", genesis.federation_id);
    println!("  Validators: {validators}");
    println!("  Threshold: {threshold}");
    println!("  Epoch length: {epoch_length}");
    println!("  Checkpoint interval: {checkpoint_interval}");
    println!();
    println!("Files:");
    println!("  {}", genesis_path.display());
    println!("  {}", devnet_marker_path.display());
    for i in 0..validators {
        println!(
            "  {}",
            output.join(format!("node-{i}.key")).display()
        );
        println!("  {}", output.join(format!("node-{i}.env")).display());
    }
    println!();
    println!("WARNING: These keys are for devnet use only. Do NOT use in production.");
}

fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
