//! Storage commands: content-addressed file store, quota management.

use clap::Subcommand;

use crate::config::Config;
use crate::output::{Context, abbrev_hex, format_number};

use super::{api_url, get_json, http_client, post_json};

#[derive(Subcommand)]
pub enum StorageCommand {
    /// Upload a file (nameless write). Prints content hash.
    Write {
        /// Path to the file to upload.
        file: String,
    },

    /// Read a file by content hash. Write to file or stdout.
    Read {
        /// Content hash (hex or base58).
        hash: String,

        /// Output file path (omit for stdout).
        #[arg(short, long)]
        output: Option<String>,
    },

    /// Atomic splice: replace bytes at offset, print new hash.
    Splice {
        /// Content hash of the existing object.
        hash: String,

        /// Byte offset to splice at.
        offset: u64,

        /// Path to file containing replacement bytes.
        file: String,
    },

    /// Delete a stored object (reveal nullifier). Prints refund amount.
    Delete {
        /// Content hash of the object to delete.
        hash: String,
    },

    /// Show quota usage (bytes stored, computrons used, remaining).
    Quota {
        #[command(subcommand)]
        command: Option<QuotaCommand>,
    },

    /// Show storage node status (capacity, usage, peers).
    Info,
}

#[derive(Subcommand)]
pub enum QuotaCommand {
    /// Add computrons to storage quota.
    TopUp {
        /// Amount of computrons to add.
        amount: u64,
    },
}

pub async fn run(
    cmd: StorageCommand,
    cfg: &Config,
    ctx: &Context,
) -> Result<(), Box<dyn std::error::Error>> {
    match cmd {
        StorageCommand::Write { file } => write_file(cfg, ctx, &file).await,
        StorageCommand::Read { hash, output } => read_file(cfg, ctx, &hash, output).await,
        StorageCommand::Splice { hash, offset, file } => {
            splice(cfg, ctx, &hash, offset, &file).await
        }
        StorageCommand::Delete { hash } => delete(cfg, ctx, &hash).await,
        StorageCommand::Quota { command } => match command {
            Some(QuotaCommand::TopUp { amount }) => quota_topup(cfg, ctx, amount).await,
            None => quota_show(cfg, ctx).await,
        },
        StorageCommand::Info => info(cfg, ctx).await,
    }
}

async fn write_file(
    cfg: &Config,
    ctx: &Context,
    file: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let content = std::fs::read(file).map_err(|e| format!("Could not read '{}': {}", file, e))?;

    let size = content.len();
    let spinner = ctx.spinner(&format!(
        "Uploading {} ({} bytes)...",
        file,
        format_number(size as u64)
    ));

    let client = http_client();
    let url = api_url(cfg, "/files/write");
    let resp = client
        .post(&url)
        .header("content-type", "application/octet-stream")
        .body(content)
        .send()
        .await?;

    if !resp.status().is_success() {
        spinner.finish_and_clear();
        let status = resp.status();
        let body = resp.text().await.unwrap_or_default();
        return Err(format!("HTTP {status}: {body}").into());
    }

    let data: serde_json::Value = resp.json().await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let hash = data["hash"].as_str().unwrap_or("?");
    let stored_size = data["size"].as_u64().unwrap_or(size as u64);

    ctx.success("File stored:");
    ctx.kv("Hash", hash);
    ctx.kv("Size", &format!("{} bytes", format_number(stored_size)));
    ctx.info(&format!("  Retrieve with: pyana storage read {}", hash));

    Ok(())
}

async fn read_file(
    cfg: &Config,
    ctx: &Context,
    hash: &str,
    output: Option<String>,
) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner(&format!("Fetching {}...", abbrev_hex(hash, 8, 4)));

    let client = http_client();
    let url = api_url(cfg, &format!("/files/read/{}", hash));
    let resp = client.get(&url).send().await?;

    if !resp.status().is_success() {
        spinner.finish_and_clear();
        let status = resp.status();
        let body = resp.text().await.unwrap_or_default();
        return Err(format!("HTTP {status}: {body}").into());
    }

    let bytes = resp.bytes().await?;
    spinner.finish_and_clear();

    match output {
        Some(path) => {
            std::fs::write(&path, &bytes)?;
            ctx.success(&format!(
                "Written {} bytes to {}",
                format_number(bytes.len() as u64),
                path
            ));
        }
        None => {
            // Write raw bytes to stdout.
            use std::io::Write;
            std::io::stdout().write_all(&bytes)?;
        }
    }

    Ok(())
}

async fn splice(
    cfg: &Config,
    ctx: &Context,
    hash: &str,
    offset: u64,
    file: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let patch_data =
        std::fs::read(file).map_err(|e| format!("Could not read '{}': {}", file, e))?;

    let spinner = ctx.spinner(&format!(
        "Splicing {} bytes at offset {} into {}...",
        patch_data.len(),
        offset,
        abbrev_hex(hash, 8, 4)
    ));

    let body = serde_json::json!({
        "hash": hash,
        "offset": offset,
        "data": bs58::encode(&patch_data).into_string(),
    });
    let data = post_json(cfg, "/files/splice", &body).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let new_hash = data["hash"].as_str().unwrap_or("?");
    let new_size = data["size"].as_u64().unwrap_or(0);

    ctx.success("Splice complete:");
    ctx.kv("Old hash", &abbrev_hex(hash, 8, 4));
    ctx.kv("New hash", new_hash);
    ctx.kv("New size", &format!("{} bytes", format_number(new_size)));

    Ok(())
}

async fn delete(cfg: &Config, ctx: &Context, hash: &str) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner(&format!("Deleting {}...", abbrev_hex(hash, 8, 4)));
    let body = serde_json::json!({
        "hash": hash,
    });
    let data = post_json(cfg, "/files/delete", &body).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let refund = data["refund_computrons"].as_u64().unwrap_or(0);
    ctx.success(&format!("Deleted object: {}", abbrev_hex(hash, 8, 4)));
    if refund > 0 {
        ctx.kv("Refund", &format!("{} computrons", format_number(refund)));
    }

    Ok(())
}

async fn quota_show(cfg: &Config, ctx: &Context) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner("Fetching storage quota...");
    let data = get_json(cfg, "/storage/quota").await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let bytes_stored = data["bytes_stored"].as_u64().unwrap_or(0);
    let bytes_limit = data["bytes_limit"].as_u64().unwrap_or(0);
    let computrons_used = data["computrons_used"].as_u64().unwrap_or(0);
    let computrons_remaining = data["computrons_remaining"].as_u64().unwrap_or(0);
    let object_count = data["object_count"].as_u64().unwrap_or(0);

    let usage_pct = if bytes_limit > 0 {
        (bytes_stored as f64 / bytes_limit as f64 * 100.0) as u64
    } else {
        0
    };

    ctx.header("Storage Quota");
    ctx.kv(
        "Bytes stored",
        &format!(
            "{} / {} ({}%)",
            format_number(bytes_stored),
            format_number(bytes_limit),
            usage_pct
        ),
    );
    ctx.kv("Objects", &format_number(object_count));
    ctx.kv("Computrons used", &format_number(computrons_used));
    ctx.kv("Remaining", &format_number(computrons_remaining));

    if usage_pct > 90 {
        ctx.warn("Storage quota nearly exhausted! Use `pyana storage quota top-up` to add more.");
    }

    Ok(())
}

async fn quota_topup(
    cfg: &Config,
    ctx: &Context,
    amount: u64,
) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner(&format!(
        "Adding {} computrons to storage quota...",
        format_number(amount)
    ));
    let body = serde_json::json!({
        "amount": amount,
    });
    let data = post_json(cfg, "/storage/quota/topup", &body).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let new_remaining = data["computrons_remaining"].as_u64().unwrap_or(0);
    ctx.success(&format!(
        "Added {} computrons to storage quota",
        format_number(amount)
    ));
    ctx.kv("New remaining", &format_number(new_remaining));

    Ok(())
}

async fn info(cfg: &Config, ctx: &Context) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner("Fetching storage node info...");
    let data = get_json(cfg, "/storage/info").await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let capacity = data["capacity_bytes"].as_u64().unwrap_or(0);
    let used = data["used_bytes"].as_u64().unwrap_or(0);
    let peer_count = data["peer_count"].as_u64().unwrap_or(0);
    let replication = data["replication_factor"].as_u64().unwrap_or(1);
    let status = data["status"].as_str().unwrap_or("unknown");

    let usage_pct = if capacity > 0 {
        (used as f64 / capacity as f64 * 100.0) as u64
    } else {
        0
    };

    ctx.header("Storage Node");
    ctx.kv("Status", status);
    ctx.kv("Capacity", &format!("{} bytes", format_number(capacity)));
    ctx.kv(
        "Used",
        &format!("{} bytes ({}%)", format_number(used), usage_pct),
    );
    ctx.kv("Peers", &peer_count.to_string());
    ctx.kv("Replication", &format!("{}x", replication));

    Ok(())
}
