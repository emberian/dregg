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
    public_key: String,
    token_id: String,
    balance: u64,
}

/// The complete genesis configuration.
#[derive(Serialize)]
struct GenesisConfig {
    /// Hex-encoded 32-byte federation id, derived from the sorted committee
    /// public keys via [`dregg_federation::derive_federation_id`]. Closes
    /// audit finding F1: not random bytes anymore.
    federation_id: String,
    /// The committee epoch this id was minted for. Always 0 at genesis;
    /// rotated by epoch transitions which mint a fresh id.
    committee_epoch: u64,
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

    // Generate keypairs for each validator. Federation_id is derived from
    // the committee pubkeys AFTER this loop — see below.
    let mut genesis_validators = Vec::with_capacity(validators);
    let mut committee_pubkeys: Vec<dregg_types::PublicKey> = Vec::with_capacity(validators);

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
        let xmss_root = blake3::derive_key("dregg-devnet-xmss-root-v1", &key_bytes);
        let xmss_root_hex = hex_encode(&xmss_root);

        committee_pubkeys.push(dregg_types::PublicKey(public_key.to_bytes()));
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
             DREGG_NODE_INDEX={i}\n\
             DREGG_FEDERATION_SIZE={validators}\n\
             DREGG_FEDERATION_PEERS={peers}\n\
             DREGG_DATA_DIR=/data\n\
             DREGG_PORT=8420\n\
             DREGG_GOSSIP_PORT=9420\n",
            peers = peers.join(","),
        );
        std::fs::write(&env_path, &env_content).unwrap_or_else(|e| {
            eprintln!("error: failed to write {}: {e}", env_path.display());
            std::process::exit(1);
        });
    }

    // BFT quorum threshold: n - floor((n-1)/3) for n validators.
    let threshold = dregg_federation::quorum_threshold(validators);

    // Derive federation_id = H(sorted committee pubkeys || epoch=0).
    // Closes audit F1: federation_id is now a commitment to the committee,
    // not random bytes. Adding/removing/rekeying a member changes the id.
    let committee_epoch: u64 = 0;
    let federation_id_bytes =
        dregg_federation::derive_federation_id_with_epoch(&committee_pubkeys, committee_epoch);
    let federation_id = hex_encode(&federation_id_bytes);

    // Build genesis config.
    //
    // Seed a non-empty ledger so a freshly-deployed devnet boots with real
    // cells (the explorer / `/api/cells` is not empty on first run). Every
    // cell here is a REAL canonical hosted cell: its `id` is the
    // content-addressed `CellId::derive_raw(public_key, token_id)` that the
    // executor will recompute and accept, not a label. The faucet cell holds
    // the genesis supply; the demo agent cells are backed by real Ed25519
    // keypairs (written to `agent-<name>.key`) so they are actually spendable
    // for demos, not just display rows.
    let default_token_id = [0u8; 32];

    // The faucet cell. Its key is deterministic so the running node / faucet
    // endpoint can locate it, but it is still a real derived CellId.
    let faucet_secret = blake3::derive_key("dregg-devnet-faucet-key-v1", b"genesis");
    let faucet_signing = ed25519_dalek::SigningKey::from_bytes(&faucet_secret);
    let faucet_pubkey = faucet_signing.verifying_key().to_bytes();
    write_key_file(output, "faucet.key", &faucet_secret);

    let mut initial_cells = vec![GenesisCell {
        id: derive_cell_id(&faucet_pubkey, &default_token_id),
        public_key: hex_encode(&faucet_pubkey),
        token_id: hex_encode(&default_token_id),
        balance: 1_000_000,
    }];

    // A handful of demo agent cells with starting balances.
    for (name, balance) in [("alice", 50_000u64), ("bob", 25_000u64), ("carol", 10_000u64)] {
        let mut key_bytes = [0u8; 32];
        getrandom::fill(&mut key_bytes).expect("getrandom failed");
        let signing = ed25519_dalek::SigningKey::from_bytes(&key_bytes);
        let pubkey = signing.verifying_key().to_bytes();
        write_key_file(output, &format!("agent-{name}.key"), &key_bytes);
        initial_cells.push(GenesisCell {
            id: derive_cell_id(&pubkey, &default_token_id),
            public_key: hex_encode(&pubkey),
            token_id: hex_encode(&default_token_id),
            balance,
        });
    }

    let genesis = GenesisConfig {
        federation_id,
        committee_epoch,
        epoch_length,
        checkpoint_interval,
        validators: genesis_validators,
        threshold,
        initial_cells,
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
        println!("  {}", output.join(format!("node-{i}.key")).display());
        println!("  {}", output.join(format!("node-{i}.env")).display());
    }
    println!();
    println!("WARNING: These keys are for devnet use only. Do NOT use in production.");
}

fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Derive the canonical content-addressed `CellId` for a hosted cell, using the
/// exact same path the runtime (`materialize_genesis_cells`) recomputes:
/// `dregg_cell::Cell::with_balance(pk, token, _).id()`. This guarantees the
/// `id` written into genesis.json matches the executor's derivation, so the
/// cell materializes instead of being rejected as a mismatched id.
fn derive_cell_id(public_key: &[u8; 32], token_id: &[u8; 32]) -> String {
    let cell = dregg_cell::Cell::with_balance(*public_key, *token_id, 0);
    hex_encode(&cell.id().0)
}

/// Write a raw 32-byte key file with owner-only (0o600) permissions.
fn write_key_file(output: &Path, name: &str, key_bytes: &[u8; 32]) {
    let key_path = output.join(name);
    std::fs::write(&key_path, key_bytes).unwrap_or_else(|e| {
        eprintln!("error: failed to write {}: {e}", key_path.display());
        std::process::exit(1);
    });
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&key_path, std::fs::Permissions::from_mode(0o600)).unwrap_or_else(
            |e| {
                eprintln!(
                    "error: failed to set permissions on {}: {e}",
                    key_path.display()
                );
                std::process::exit(1);
            },
        );
    }
}
