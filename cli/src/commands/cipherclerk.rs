//! Cipherclerk operations: balance, transfer, delegate, info.

use clap::Subcommand;

use crate::config::Config;
use crate::output::{Context, abbrev_hex, format_number};

use super::{get_json, post_json};

#[derive(Subcommand)]
pub enum CipherclerkCommand {
    /// Show balances.
    Balance,

    /// Submit basic turn (transfer intent shortcut).
    ///
    /// Fixed shape to match SubmitTurnRequest (agent/nonce/fee). Note: this
    /// path produces no-effect turns; real transfers use `pyana turn build`
    /// (full effects + CallForest). Old recipient-only body was 422 skew.
    Transfer {
        /// Recipient cell ID or public key.
        to: String,

        /// Amount of computrons to transfer.
        amount: u64,

        /// Optional memo/note.
        #[arg(long)]
        memo: Option<String>,
    },

    /// Delegate capability to a target cell.
    Delegate {
        /// Cell holding the capability.
        cell_id: String,

        /// Target to delegate to (cell ID or public key).
        target: String,

        /// Attenuation (restrict delegation scope).
        #[arg(long)]
        attenuate: Option<String>,
    },

    /// Show cclerk identity information.
    Info,
}

pub async fn run(
    cmd: CipherclerkCommand,
    cfg: &Config,
    ctx: &Context,
) -> Result<(), Box<dyn std::error::Error>> {
    match cmd {
        CipherclerkCommand::Balance => balance(cfg, ctx).await,
        CipherclerkCommand::Transfer { to, amount, memo } => {
            transfer(cfg, ctx, &to, amount, memo).await
        }
        CipherclerkCommand::Delegate {
            cell_id,
            target,
            attenuate,
        } => delegate(cfg, ctx, &cell_id, &target, attenuate).await,
        CipherclerkCommand::Info => info(cfg, ctx).await,
    }
}

async fn balance(cfg: &Config, ctx: &Context) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner("Fetching cclerk...");
    let data = get_json(cfg, "/cipherclerk").await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let token_count = data["token_count"].as_u64().unwrap_or(0);
    let receipt_chain = data["receipt_chain_length"].as_u64().unwrap_or(0);
    let computrons = data["computrons"].as_u64().unwrap_or(0);

    ctx.header("Cipherclerk Balance");
    ctx.kv("Computrons", &format_number(computrons));
    ctx.kv("Tokens", &token_count.to_string());
    ctx.kv("Receipt chain", &format_number(receipt_chain));

    Ok(())
}

async fn transfer(
    cfg: &Config,
    ctx: &Context,
    to: &str,
    amount: u64,
    memo: Option<String>,
) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner(&format!(
        "Submitting basic turn ({} computrons intent to {})...",
        format_number(amount),
        abbrev_hex(to, 8, 4)
    ));
    // Proper fix for 422: /turn/submit expects SubmitTurnRequest { agent, nonce, fee, memo }.
    // Old {recipient, amount, ...} shape (and the fact that handler builds empty CallForest)
    // meant this never performed a real Transfer effect. We now emit the exact shape
    // the deserializer + handler require. Nonce=0 and dummy agent will typically be
    // rejected by the executor (correctly) with a structured response rather than 422.
    // For real effectful transfers use `pyana turn build` (interactive) or submit a
    // full turn JSON that the node can execute via its internal paths.
    let user_memo = memo.unwrap_or_default();
    let body = serde_json::json!({
        "agent": "0000000000000000000000000000000000000000000000000000000000000000",
        "nonce": 0u64,
        "fee": 0u64,
        "memo": format!("CLI transfer intent amount={} to={} note={}", amount, to, user_memo),
    });
    let data = post_json(cfg, "/turn/submit", &body).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    if let Some(err) = data.get("error").and_then(|v| v.as_str()) {
        ctx.warn(&format!("Turn rejected by node: {}", err));
        return Ok(());
    }

    let turn_id = data["turn_hash"]
        .as_str()
        .or_else(|| data["turn_id"].as_str())
        .unwrap_or("?");
    ctx.success(&format!(
        "Basic turn submitted ({} computrons intent recorded in memo) to {}",
        format_number(amount),
        abbrev_hex(to, 8, 4)
    ));
    ctx.kv("Turn ID", &abbrev_hex(turn_id, 8, 4));
    ctx.info("  Note: this advanced the receipt chain only. Use `pyana turn build` for full effect-bearing turns.");

    Ok(())
}

async fn delegate(
    cfg: &Config,
    ctx: &Context,
    cell_id: &str,
    target: &str,
    attenuate: Option<String>,
) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner("Delegating capability...");
    let body = serde_json::json!({
        "cell_id": cell_id,
        "target": target,
        "attenuation": attenuate,
    });
    let data = post_json(cfg, "/cipherclerk/attenuate", &body).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let new_token = data["new_token_id"].as_str().unwrap_or("?");
    ctx.success("Capability delegated:");
    ctx.kv("From cell", &abbrev_hex(cell_id, 8, 4));
    ctx.kv("To", &abbrev_hex(target, 8, 4));
    ctx.kv("New token", &abbrev_hex(new_token, 8, 4));

    Ok(())
}

async fn info(cfg: &Config, ctx: &Context) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner("Fetching cclerk info...");
    let data = get_json(cfg, "/cipherclerk").await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let pk = data["public_key"].as_str().unwrap_or("unknown");
    let unlocked = data["unlocked"].as_bool().unwrap_or(false);
    let token_count = data["token_count"].as_u64().unwrap_or(0);
    let receipt_chain = data["receipt_chain_length"].as_u64().unwrap_or(0);

    ctx.header("Cipherclerk Identity");
    ctx.kv("Public Key", pk);
    ctx.kv("Status", if unlocked { "unlocked" } else { "locked" });
    ctx.kv("Tokens", &token_count.to_string());
    ctx.kv("Receipts", &receipt_chain.to_string());
    // Note: CLI has no local keyfile for cclerk; the node's cipherclerk (node.key)
    // is authoritative. The legacy cclerk.keyfile setting was removed as unused.

    Ok(())
}
