//! Proof commands: verify, inspect, export, chain.

use clap::Subcommand;

use crate::config::Config;
use crate::output::{Context, TreeNode, abbrev_hex, format_number};

use super::{get_json, post_json};

#[derive(Subcommand)]
pub enum ProofCommand {
    /// Verify a STARK proof from file. Prints result and public inputs.
    Verify {
        /// Path to proof file (JSON or binary).
        proof_file: String,
    },

    /// Show proof metadata (size, constraints, public inputs).
    Inspect {
        /// Path to proof file.
        proof_file: String,
    },

    /// Export the proof for a turn to a file.
    Export {
        /// Turn ID (hex hash).
        turn_id: String,

        /// Output file path (default: <turn_id>.proof.json).
        #[arg(short, long)]
        output: Option<String>,
    },

    /// Show the proof chain for a cell's history (IVC).
    Chain {
        /// Cell ID.
        cell_id: String,

        /// Maximum number of proofs to show.
        #[arg(long, default_value = "20")]
        limit: usize,
    },
}

pub async fn run(
    cmd: ProofCommand,
    cfg: &Config,
    ctx: &Context,
) -> Result<(), Box<dyn std::error::Error>> {
    match cmd {
        ProofCommand::Verify { proof_file } => verify(cfg, ctx, &proof_file).await,
        ProofCommand::Inspect { proof_file } => inspect(ctx, &proof_file),
        ProofCommand::Export { turn_id, output } => export(cfg, ctx, &turn_id, output).await,
        ProofCommand::Chain { cell_id, limit } => chain(cfg, ctx, &cell_id, limit).await,
    }
}

async fn verify(
    cfg: &Config,
    ctx: &Context,
    proof_file: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let content =
        std::fs::read(proof_file).map_err(|e| format!("Could not read '{}': {}", proof_file, e))?;

    let spinner = ctx.spinner("Verifying proof...");

    // Try parsing as JSON first; if that fails, send as binary.
    let proof_json: serde_json::Value = match serde_json::from_slice(&content) {
        Ok(v) => v,
        Err(_) => {
            // Encode binary proof as base58 for submission.
            serde_json::json!({
                "proof_binary": bs58::encode(&content).into_string(),
            })
        }
    };

    let data = post_json(cfg, "/proof/verify", &proof_json).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let valid = data["valid"].as_bool().unwrap_or(false);
    let public_inputs = &data["public_inputs"];

    if valid {
        ctx.success("Proof is VALID");
    } else {
        ctx.error("Proof is INVALID");
        if let Some(reason) = data["reason"].as_str() {
            ctx.kv("Reason", reason);
        }
    }

    // Show public inputs.
    if let Some(inputs) = public_inputs.as_array() {
        if !inputs.is_empty() {
            ctx.header("Public Inputs");
            for (i, input) in inputs.iter().enumerate() {
                let val = match input {
                    serde_json::Value::String(s) => s.clone(),
                    other => other.to_string(),
                };
                ctx.kv(&format!("[{}]", i), &val);
            }
        }
    }

    Ok(())
}

fn inspect(ctx: &Context, proof_file: &str) -> Result<(), Box<dyn std::error::Error>> {
    let content =
        std::fs::read(proof_file).map_err(|e| format!("Could not read '{}': {}", proof_file, e))?;

    let file_size = content.len();

    // Try JSON parse.
    let metadata = if let Ok(json) = serde_json::from_slice::<serde_json::Value>(&content) {
        json
    } else {
        // Binary proof -- compute hash and report size.
        let hash = blake3::hash(&content);
        serde_json::json!({
            "format": "binary",
            "hash": hash.to_hex().to_string(),
            "size": file_size,
        })
    };

    if ctx.mode == crate::output::Mode::Json {
        ctx.json_stdout(&metadata);
        return Ok(());
    }

    let format = metadata["format"]
        .as_str()
        .or_else(|| metadata["proof_type"].as_str())
        .unwrap_or("unknown");
    let constraints = metadata["num_constraints"].as_u64().unwrap_or(0);
    let public_input_count = metadata["public_inputs"]
        .as_array()
        .map(|a| a.len())
        .unwrap_or(0);
    let hash = metadata["hash"]
        .as_str()
        .or_else(|| metadata["commitment"].as_str())
        .unwrap_or("(computed on verify)");

    let title = format!("Proof: {}", proof_file);
    let size_str = format!("{} bytes", format_number(file_size as u64));
    let constraints_str = if constraints > 0 {
        format_number(constraints)
    } else {
        "-".to_string()
    };
    let inputs_str = public_input_count.to_string();

    ctx.boxed(
        &title,
        &[
            ("Format", format),
            ("Size", &size_str),
            ("Constraints", &constraints_str),
            ("Public inputs", &inputs_str),
            ("Hash", hash),
        ],
    );

    Ok(())
}

async fn export(
    cfg: &Config,
    ctx: &Context,
    turn_id: &str,
    output: Option<String>,
) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner(&format!(
        "Exporting proof for turn {}...",
        abbrev_hex(turn_id, 8, 4)
    ));
    let data = get_json(cfg, &format!("/proof/export/{}", turn_id)).await?;
    spinner.finish_and_clear();

    let out_path = output.unwrap_or_else(|| format!("{}.proof.json", turn_id));
    let json_str = serde_json::to_string_pretty(&data)?;
    std::fs::write(&out_path, &json_str)?;

    if cfg.is_json() {
        ctx.json_stdout(&serde_json::json!({
            "path": out_path,
            "size": json_str.len(),
            "turn_id": turn_id,
        }));
        return Ok(());
    }

    ctx.success(&format!("Proof exported to: {}", out_path));
    ctx.kv("Turn", &abbrev_hex(turn_id, 8, 4));
    ctx.kv(
        "Size",
        &format!("{} bytes", format_number(json_str.len() as u64)),
    );

    Ok(())
}

async fn chain(
    cfg: &Config,
    ctx: &Context,
    cell_id: &str,
    limit: usize,
) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner(&format!(
        "Fetching IVC proof chain for {}...",
        abbrev_hex(cell_id, 8, 4)
    ));
    let data = get_json(cfg, &format!("/proof/chain/{}", cell_id)).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let empty = vec![];
    let proofs = data["proofs"].as_array().unwrap_or(&empty);

    if proofs.is_empty() {
        ctx.info(&format!(
            "No proof chain found for cell {}.",
            abbrev_hex(cell_id, 8, 4)
        ));
        return Ok(());
    }

    ctx.header(&format!(
        "IVC Proof Chain: {} ({} steps)",
        abbrev_hex(cell_id, 8, 4),
        proofs.len()
    ));

    let displayed: Vec<&serde_json::Value> = proofs.iter().take(limit).collect();
    let children: Vec<TreeNode> = displayed
        .iter()
        .enumerate()
        .map(|(_i, p)| {
            let height = p["height"].as_u64().unwrap_or(0);
            let turn_hash = p["turn_hash"].as_str().unwrap_or("?");
            let proof_hash = p["proof_hash"].as_str().unwrap_or("?");
            let valid = p["valid"].as_bool().unwrap_or(true);

            let status = if valid { "ok" } else { "INVALID" };
            let label = format!(
                "#{} turn={} proof={} [{}]",
                height,
                abbrev_hex(turn_hash, 6, 4),
                abbrev_hex(proof_hash, 6, 4),
                status,
            );
            TreeNode::leaf(label)
        })
        .collect();

    let root_label = format!("Cell {} (IVC)", abbrev_hex(cell_id, 8, 4));
    ctx.tree(&root_label, &children);

    if proofs.len() > limit {
        ctx.info(&format!(
            "  Showing {} of {} proofs. Use --limit to see more.",
            limit,
            proofs.len()
        ));
    }

    Ok(())
}
