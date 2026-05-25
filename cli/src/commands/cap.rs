//! Capability management commands (export, enliven, handoff).

use clap::Subcommand;

use crate::config::Config;
use crate::output::{Context, abbrev_hex};

use super::{get_json, post_json};

#[derive(Subcommand)]
pub enum CapCommand {
    /// Export a cell as a pyana:// sturdy reference URI.
    Export {
        /// Cell ID to export.
        cell_id: String,

        /// Optional attenuation (restrict what the recipient can do).
        #[arg(long)]
        attenuate: Option<String>,
    },

    /// Enliven a pyana:// sturdy reference URI.
    Enliven {
        /// The pyana:// URI to enliven.
        uri: String,
    },

    /// Create a handoff certificate for transferring capability.
    Handoff {
        /// Source cell ID.
        cell_id: String,

        /// Recipient's public key (hex).
        recipient_pk: String,
    },

    /// List held capabilities.
    List,

    /// Revoke a capability (by cell ID or cap ID).
    Revoke {
        /// Cell or capability ID to revoke.
        id: String,
    },
}

pub async fn run(
    cmd: CapCommand,
    cfg: &Config,
    ctx: &Context,
) -> Result<(), Box<dyn std::error::Error>> {
    match cmd {
        CapCommand::Export { cell_id, attenuate } => export(cfg, ctx, &cell_id, attenuate).await,
        CapCommand::Enliven { uri } => enliven(cfg, ctx, &uri).await,
        CapCommand::Handoff {
            cell_id,
            recipient_pk,
        } => handoff(cfg, ctx, &cell_id, &recipient_pk).await,
        CapCommand::List => list(cfg, ctx).await,
        CapCommand::Revoke { id } => revoke(cfg, ctx, &id).await,
    }
}

async fn export(
    cfg: &Config,
    ctx: &Context,
    cell_id: &str,
    attenuate: Option<String>,
) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner("Generating sturdy reference...");

    let body = serde_json::json!({
        "cell_id": cell_id,
        "attenuation": attenuate,
    });
    let data = post_json(cfg, "/turns/bearer-auth", &body).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    // Construct the pyana:// URI from response data.
    let node_id = data["node_id"].as_str().unwrap_or("local");
    let secret = data["secret"].as_str().unwrap_or("?");

    let uri = format!("pyana://{}/{}/{}", node_id, cell_id, secret);

    ctx.success("Exported sturdy reference:");
    eprintln!("  {}", console::style(&uri).cyan().bold());
    eprintln!();
    ctx.info("Share this URI to grant access. Recipient uses:");
    eprintln!(
        "  {}",
        console::style(format!("pyana cap enliven \"{}\"", &uri)).dim()
    );

    Ok(())
}

async fn enliven(cfg: &Config, ctx: &Context, uri: &str) -> Result<(), Box<dyn std::error::Error>> {
    // Parse the pyana:// URI.
    if !uri.starts_with("pyana://") {
        return Err("Invalid URI: must start with pyana://".into());
    }

    let parts: Vec<&str> = uri.trim_start_matches("pyana://").split('/').collect();
    if parts.len() < 3 {
        return Err("Invalid URI format. Expected: pyana://<node>/<cell>/<secret>".into());
    }

    let node_id = parts[0];
    let cell_id = parts[1];
    let secret = parts[2];

    let spinner = ctx.spinner("Enlivening capability...");
    let body = serde_json::json!({
        "node_id": node_id,
        "cell_id": cell_id,
        "secret": secret,
    });
    let data = post_json(cfg, "/turns/peer-exchange", &body).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let cap_id = data["cap_id"].as_str().unwrap_or("?");
    ctx.success(&format!(
        "Capability enlivened: {}",
        abbrev_hex(cap_id, 8, 4)
    ));
    ctx.kv("Cell", &abbrev_hex(cell_id, 8, 4));
    ctx.kv("Node", node_id);
    ctx.info("  You can now invoke methods on this cell.");

    Ok(())
}

async fn handoff(
    cfg: &Config,
    ctx: &Context,
    cell_id: &str,
    recipient_pk: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner("Creating handoff certificate...");
    let body = serde_json::json!({
        "cell_id": cell_id,
        "recipient_pk": recipient_pk,
    });
    let data = post_json(cfg, "/turns/peer-exchange", &body).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let cert_hash = data["certificate_hash"].as_str().unwrap_or("?");
    ctx.success("Handoff certificate created:");
    ctx.kv("Cell", &abbrev_hex(cell_id, 8, 4));
    ctx.kv("Recipient", &abbrev_hex(recipient_pk, 8, 4));
    ctx.kv("Certificate", &abbrev_hex(cert_hash, 8, 4));

    Ok(())
}

async fn list(cfg: &Config, ctx: &Context) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner("Fetching capabilities...");
    let data = get_json(cfg, "/cipherclerk/tokens").await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let empty = vec![];
    let tokens = data.as_array().unwrap_or(&empty);
    if tokens.is_empty() {
        ctx.info("No capabilities held. Use `pyana cap enliven` to add one.");
        return Ok(());
    }

    ctx.header(&format!("Capabilities ({})", tokens.len()));
    let rows: Vec<Vec<String>> = tokens
        .iter()
        .map(|t| {
            let id = t["id"].as_str().unwrap_or("?");
            let label = t["label"].as_str().unwrap_or("-");
            let service = t["service"].as_str().unwrap_or("?");
            vec![abbrev_hex(id, 8, 4), label.to_string(), service.to_string()]
        })
        .collect();

    ctx.table(&["ID", "Label", "Service"], &rows);

    Ok(())
}

async fn revoke(cfg: &Config, ctx: &Context, id: &str) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner("Revoking capability...");
    let body = serde_json::json!({
        "token_id": id,
    });
    let data = post_json(cfg, "/cipherclerk/attenuate", &body).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    ctx.success(&format!("Revoked capability: {}", abbrev_hex(id, 8, 4)));

    Ok(())
}
