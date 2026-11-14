//! Turn building and submission commands.
//!
//! The `dregg` CLI drives the node's `/turn/submit` JSON ingress: the node
//! builds a real signed call-forest from the submitted actions, executes it,
//! gossips it, and submits it to the blocklace for consensus ordering. On
//! finalization the commit path runs the configured state producer (the
//! verified Lean executor when `DREGG_LEAN_PRODUCER=1`) and, when full-turn
//! proving is enabled, generates + verifies a STARK proof for the turn.
//!
//! The JSON ingress covers the "thin client" effect set — state writes, value
//! transfers, nonce bumps, and event emission. Richer effects (capability
//! grants, notes, factory births, CapTP) go through the SDK's signed-envelope
//! `/turns/submit` path (a typed `SignedTurn`), which the CLI surfaces but does
//! not hand-build (it needs app-level keys the CLI does not hold).

use clap::Subcommand;
use dialoguer::{Confirm, Input, Select};

use crate::config::Config;
use crate::output::{Context, abbrev_hex};

use super::{get_json, post_json};

/// Effect kinds the node's `/turn/submit` JSON ingress accepts (the
/// `TurnEffectSpec` set in node/src/api.rs). Keep in sync with the node.
const JSON_EFFECT_KINDS: &[&str] = &["transfer", "set_field", "emit_event", "increment_nonce"];

#[derive(Subcommand)]
pub enum TurnCommand {
    /// Submit a turn from a JSON file (a `SubmitTurnRequest`, or `{effects:[...]}`).
    ///
    /// The file may be either a full request shape
    /// (`{nonce, fee, actions:[{effects:[{kind,...}]}]}`) or a convenience
    /// shorthand (`{effects:[{kind,...}]}` / `{actions:[...]}`), which the CLI
    /// normalizes into a single-action request.
    Submit {
        /// Path to a JSON file describing the turn.
        file: String,
        /// Override the turn fee (computrons).
        #[arg(long, default_value_t = 0)]
        fee: u64,
        /// Override the turn nonce.
        #[arg(long, default_value_t = 0)]
        nonce: u64,
        /// Optional memo string.
        #[arg(long)]
        memo: Option<String>,
    },

    /// Submit a single effect quickly from flags (no file, no prompts).
    ///
    /// Examples:
    ///   dregg turn quick transfer --to <cell> --amount 100
    ///   dregg turn quick set-field --index 0 --value 42
    ///   dregg turn quick emit-event --topic ping
    ///   dregg turn quick increment-nonce
    Quick {
        #[command(subcommand)]
        effect: QuickEffect,
        /// Target cell (defaults to the node operator's own agent cell).
        #[arg(long)]
        target: Option<String>,
        /// Turn fee (computrons).
        #[arg(long, default_value_t = 0)]
        fee: u64,
    },

    /// Check turn receipt status (by turn hash).
    Status {
        /// Turn hash (hex).
        turn_id: String,
    },

    /// Interactive turn builder (guided prompts).
    Build,
}

#[derive(Subcommand)]
pub enum QuickEffect {
    /// Transfer computrons to another cell.
    Transfer {
        /// Recipient cell id (hex).
        #[arg(long)]
        to: String,
        /// Amount in computrons.
        #[arg(long)]
        amount: u64,
        /// Source cell (defaults to the action target).
        #[arg(long)]
        from: Option<String>,
    },
    /// Write a field-element value into a cell state slot.
    SetField {
        /// State slot index.
        #[arg(long)]
        index: u64,
        /// Value (decimal, 0x-hex scalar, or 64-char hex field element).
        #[arg(long)]
        value: String,
    },
    /// Emit an event (topic + optional data words).
    EmitEvent {
        /// Event topic string.
        #[arg(long)]
        topic: String,
        /// Data words (decimal/hex scalars), repeatable.
        #[arg(long = "data")]
        data: Vec<String>,
    },
    /// Increment the cell's nonce by 1.
    IncrementNonce,
}

pub async fn run(
    cmd: TurnCommand,
    cfg: &Config,
    ctx: &Context,
) -> Result<(), Box<dyn std::error::Error>> {
    match cmd {
        TurnCommand::Submit {
            file,
            fee,
            nonce,
            memo,
        } => submit_file(cfg, ctx, &file, fee, nonce, memo).await,
        TurnCommand::Quick {
            effect,
            target,
            fee,
        } => quick(cfg, ctx, effect, target, fee).await,
        TurnCommand::Status { turn_id } => status(cfg, ctx, &turn_id).await,
        TurnCommand::Build => build(cfg, ctx).await,
    }
}

/// Normalize a user-supplied JSON value into a node `SubmitTurnRequest`.
///
/// Accepts the full request shape, an `{actions:[...]}` value, or a shorthand
/// `{effects:[...]}` (or a bare effects array), wrapping the latter into a
/// single action. The `agent` field is filled with a placeholder — the node
/// derives the real agent from its cipherclerk and ignores the body value.
fn normalize_request(
    mut v: serde_json::Value,
    fee: u64,
    nonce: u64,
    memo: Option<String>,
) -> Result<serde_json::Value, String> {
    use serde_json::{Value, json};

    // A bare array is treated as a list of effects.
    if let Value::Array(arr) = &v {
        v = json!({ "effects": arr });
    }

    let obj = v
        .as_object()
        .ok_or_else(|| "turn JSON must be an object or an array of effects".to_string())?;

    let actions: Value = if let Some(actions) = obj.get("actions") {
        actions.clone()
    } else if let Some(effects) = obj.get("effects") {
        // Shorthand: wrap a single effects list into one action.
        json!([{ "effects": effects }])
    } else {
        return Err(
            "turn JSON needs an `actions` array or an `effects` array (the shorthand)".to_string(),
        );
    };

    // Pull overrides from the body if the flags were left at defaults.
    let body_fee = obj.get("fee").and_then(|x| x.as_u64()).unwrap_or(fee);
    let body_nonce = obj.get("nonce").and_then(|x| x.as_u64()).unwrap_or(nonce);
    let body_memo = memo.or_else(|| {
        obj.get("memo")
            .and_then(|x| x.as_str())
            .map(|s| s.to_string())
    });

    Ok(json!({
        // Advisory only — the node derives the real signer from its cipherclerk.
        "agent": "00".repeat(32),
        "nonce": if nonce != 0 { nonce } else { body_nonce },
        "fee": if fee != 0 { fee } else { body_fee },
        "memo": body_memo,
        "actions": actions,
    }))
}

async fn submit_file(
    cfg: &Config,
    ctx: &Context,
    file: &str,
    fee: u64,
    nonce: u64,
    memo: Option<String>,
) -> Result<(), Box<dyn std::error::Error>> {
    let content =
        std::fs::read_to_string(file).map_err(|e| format!("Could not read '{}': {}", file, e))?;
    let turn_json: serde_json::Value =
        serde_json::from_str(&content).map_err(|e| format!("Invalid JSON in '{}': {}", file, e))?;
    let req = normalize_request(turn_json, fee, nonce, memo)?;
    submit_request(cfg, ctx, req).await
}

async fn quick(
    cfg: &Config,
    ctx: &Context,
    effect: QuickEffect,
    target: Option<String>,
    fee: u64,
) -> Result<(), Box<dyn std::error::Error>> {
    use serde_json::json;
    let eff = match effect {
        QuickEffect::Transfer { to, amount, from } => {
            let mut e = json!({ "kind": "transfer", "to": to, "amount": amount });
            if let Some(f) = from {
                e["from"] = json!(f);
            }
            e
        }
        QuickEffect::SetField { index, value } => {
            json!({ "kind": "set_field", "index": index, "value": value })
        }
        QuickEffect::EmitEvent { topic, data } => {
            json!({ "kind": "emit_event", "topic": topic, "data": data })
        }
        QuickEffect::IncrementNonce => json!({ "kind": "increment_nonce" }),
    };
    let mut action = json!({ "effects": [eff] });
    if let Some(t) = target {
        action["target"] = json!(t);
    }
    let req = json!({
        "agent": "00".repeat(32),
        "nonce": 0,
        "fee": fee,
        "memo": serde_json::Value::Null,
        "actions": [action],
    });
    submit_request(cfg, ctx, req).await
}

/// POST a normalized request to the node and render rich feedback (acceptance,
/// proof status, witness material), honestly surfacing the verified-ness.
async fn submit_request(
    cfg: &Config,
    ctx: &Context,
    req: serde_json::Value,
) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner("Submitting turn (sign → execute → consensus)...");
    // `/api/turns/submit` = the `/turn/submit` alias that also passes
    // gateway proxies which only forward `/api/*` (the public devnet).
    let data = post_json(cfg, "/api/turns/submit", &req).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    render_submit_response(ctx, &data);
    Ok(())
}

/// Render a `SubmitTurnResponse` with the verified-execution facts spelled out.
fn render_submit_response(ctx: &Context, data: &serde_json::Value) {
    let accepted = data["accepted"].as_bool().unwrap_or(false);
    let turn_hash = data["turn_hash"].as_str().unwrap_or("?");
    let proof_status = data["proof_status"].as_str().unwrap_or("unknown");
    let has_witness = data["has_witness"].as_bool().unwrap_or(false);
    let witness_count = data["witness_count"].as_u64().unwrap_or(0);

    if accepted {
        ctx.success(&format!("Turn committed: {}", abbrev_hex(turn_hash, 8, 4)));
    } else {
        let err = data["error"].as_str().unwrap_or(turn_hash);
        ctx.error(&format!("Turn rejected: {err}"));
    }

    ctx.header("Turn Result");
    ctx.kv("Accepted", if accepted { "yes" } else { "no" });
    ctx.kv("Turn hash", &abbrev_hex(turn_hash, 8, 4));
    ctx.kv("Proof status", &render_proof_status(proof_status));
    ctx.kv("Witnessed", if has_witness { "yes" } else { "no" });
    if witness_count > 0 {
        ctx.kv("Witness count", &witness_count.to_string());
    }
    if accepted {
        ctx.info("  Ordered into the blocklace; the commit path proves it on finalization.");
        ctx.info(&format!(
            "  Track it:  dregg turn status {}",
            abbrev_hex(turn_hash, 6, 4)
        ));
    }
}

/// Map the node's `ActivityProofStatus` enum string into an honest, readable line.
fn render_proof_status(s: &str) -> String {
    let label = match s {
        "Proved" | "proved" => "PROVED (real STARK verified)",
        "NotRequired" | "not_required" => {
            "not required (coordination; signature attestation only, no validity proof)"
        }
        "ProofGenerationFailed" | "proof_generation_failed" => "PROOF GENERATION FAILED",
        "NotCommitted" | "not_committed" => "not committed",
        other => other,
    };
    label.to_string()
}

async fn status(
    cfg: &Config,
    ctx: &Context,
    turn_id: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner("Checking turn status...");
    let data = get_json(cfg, "/api/receipts").await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    // Match against either the turn hash or receipt hash; accept an abbreviated prefix.
    let needle = turn_id.trim().to_lowercase();
    let receipts = data.as_array();
    let found = receipts.and_then(|rs| {
        rs.iter().find(|r| {
            let th = r["turn_hash"].as_str().unwrap_or("").to_lowercase();
            let rh = r["receipt_hash"].as_str().unwrap_or("").to_lowercase();
            th == needle || rh == needle || th.starts_with(&needle) || rh.starts_with(&needle)
        })
    });

    match found {
        Some(receipt) => {
            let turn_hash = receipt["turn_hash"].as_str().unwrap_or("?");
            let finality = receipt["finality"].as_str().unwrap_or("unknown");
            let computrons = receipt["computrons_used"].as_u64().unwrap_or(0);
            let actions = receipt["action_count"].as_u64().unwrap_or(0);
            let has_proof = receipt["has_proof"].as_bool().unwrap_or(false);
            let has_witness = receipt["has_witness"].as_bool().unwrap_or(false);
            let witness_count = receipt["witness_count"].as_u64().unwrap_or(0);
            let pre = receipt["pre_state"].as_str().unwrap_or("?");
            let post = receipt["post_state"].as_str().unwrap_or("?");
            let chain_index = receipt["chain_index"].as_u64().unwrap_or(0);

            ctx.header("Turn Receipt");
            ctx.kv("Turn hash", &abbrev_hex(turn_hash, 8, 4));
            ctx.kv("Finality", finality);
            ctx.kv("Chain index", &chain_index.to_string());
            ctx.kv("Actions", &actions.to_string());
            ctx.kv("Computrons", &crate::output::format_number(computrons));
            ctx.kv("Pre-state", &abbrev_hex(pre, 8, 4));
            ctx.kv("Post-state", &abbrev_hex(post, 8, 4));
            let proof_label = receipt["proof_status"]
                .as_str()
                .map(render_proof_status)
                .unwrap_or_else(|| {
                    if has_proof {
                        "present".into()
                    } else {
                        "unknown".into()
                    }
                });
            ctx.kv("Proof", &proof_label);
            ctx.kv("Witnessed", if has_witness { "yes" } else { "no" });
            if witness_count > 0 {
                ctx.kv("Witness count", &witness_count.to_string());
            }
        }
        None => {
            ctx.warn(&format!(
                "No receipt found for turn {}",
                abbrev_hex(turn_id, 8, 4)
            ));
            ctx.info("  The turn may still be pending finalization, or the hash may be wrong.");
            ctx.info("  Receipts appear after the commit path runs; try again shortly.");
        }
    }

    Ok(())
}

async fn build(cfg: &Config, ctx: &Context) -> Result<(), Box<dyn std::error::Error>> {
    ctx.header("Interactive Turn Builder");
    ctx.info("Build a turn step by step. (CLI JSON ingress covers the thin-client");
    ctx.info("effect set; richer effects go through the SDK signed-envelope path.)\n");

    let target: String = Input::new()
        .with_prompt("Target cell id (empty = your agent cell)")
        .allow_empty(true)
        .interact_text()?;

    let mut effects: Vec<serde_json::Value> = Vec::new();
    loop {
        let labels = &[
            "transfer (value)",
            "set-field (state write)",
            "emit-event",
            "increment-nonce",
        ];
        let idx = Select::new()
            .with_prompt("Add effect")
            .items(labels)
            .default(0)
            .interact()?;
        let kind = JSON_EFFECT_KINDS[idx];
        let eff = build_one_effect(kind)?;
        effects.push(eff);

        if !Confirm::new()
            .with_prompt("Add another effect?")
            .default(false)
            .interact()?
        {
            break;
        }
    }

    let fee: String = Input::new()
        .with_prompt("Fee (computrons)")
        .default("0".to_string())
        .interact_text()?;

    let mut action = serde_json::json!({ "effects": effects });
    if !target.trim().is_empty() {
        action["target"] = serde_json::json!(target.trim());
    }
    let req = serde_json::json!({
        "agent": "00".repeat(32),
        "nonce": 0,
        "fee": fee.parse::<u64>().unwrap_or(0),
        "memo": serde_json::Value::Null,
        "actions": [action],
    });

    eprintln!();
    ctx.info("Constructed request:");
    eprintln!("{}", serde_json::to_string_pretty(&req)?);
    eprintln!();

    let choices = &["Submit now", "Save to file", "Cancel"];
    let choice = Select::new()
        .with_prompt("Action")
        .items(choices)
        .default(0)
        .interact()?;

    match choice {
        0 => submit_request(cfg, ctx, req).await,
        1 => {
            let filename: String = Input::new()
                .with_prompt("Output file path")
                .default("turn.json".to_string())
                .interact_text()?;
            std::fs::write(&filename, serde_json::to_string_pretty(&req)?)?;
            ctx.success(&format!("Saved to {filename}"));
            Ok(())
        }
        _ => {
            ctx.info("Cancelled.");
            Ok(())
        }
    }
}

fn build_one_effect(kind: &str) -> Result<serde_json::Value, Box<dyn std::error::Error>> {
    use serde_json::json;
    let eff = match kind {
        "transfer" => {
            let to: String = Input::new()
                .with_prompt("Recipient cell id")
                .interact_text()?;
            let amount: u64 = Input::new()
                .with_prompt("Amount (computrons)")
                .interact_text()?;
            json!({ "kind": "transfer", "to": to, "amount": amount })
        }
        "set_field" => {
            let index: usize = Input::new()
                .with_prompt("State slot index")
                .interact_text()?;
            let value: String = Input::new()
                .with_prompt("Value (decimal / 0x-hex / 64-char field element)")
                .interact_text()?;
            json!({ "kind": "set_field", "index": index, "value": value })
        }
        "emit_event" => {
            let topic: String = Input::new().with_prompt("Event topic").interact_text()?;
            let data_raw: String = Input::new()
                .with_prompt("Data words (comma-separated, optional)")
                .allow_empty(true)
                .interact_text()?;
            let data: Vec<String> = data_raw
                .split(',')
                .map(|s| s.trim().to_string())
                .filter(|s| !s.is_empty())
                .collect();
            json!({ "kind": "emit_event", "topic": topic, "data": data })
        }
        "increment_nonce" => json!({ "kind": "increment_nonce" }),
        other => return Err(format!("unknown effect kind: {other}").into()),
    };
    Ok(eff)
}

#[cfg(test)]
mod proving_policy_tests {
    #[test]
    fn coordination_is_rendered_as_signature_only() {
        for status in ["NotRequired", "not_required"] {
            let label = super::render_proof_status(status);
            assert!(label.contains("signature attestation only"));
            assert!(label.contains("no validity proof"));
            assert!(!label.contains("PROVED"));
        }
    }
}
