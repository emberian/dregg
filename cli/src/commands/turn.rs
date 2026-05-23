//! Turn building and submission commands.

use clap::Subcommand;
use dialoguer::{Input, Select};

use crate::config::Config;
use crate::output::{Context, abbrev_hex};

use super::{get_json, post_json};

#[derive(Subcommand)]
pub enum TurnCommand {
    /// Submit a turn from a JSON file.
    Submit {
        /// Path to a JSON file describing the turn.
        file: String,
    },

    /// Check turn receipt status.
    Status {
        /// Turn ID (hex hash).
        turn_id: String,
    },

    /// Interactive turn builder (guided prompts).
    Build,
}

pub async fn run(
    cmd: TurnCommand,
    cfg: &Config,
    ctx: &Context,
) -> Result<(), Box<dyn std::error::Error>> {
    match cmd {
        TurnCommand::Submit { file } => submit(cfg, ctx, &file).await,
        TurnCommand::Status { turn_id } => status(cfg, ctx, &turn_id).await,
        TurnCommand::Build => build(cfg, ctx).await,
    }
}

async fn submit(cfg: &Config, ctx: &Context, file: &str) -> Result<(), Box<dyn std::error::Error>> {
    let content =
        std::fs::read_to_string(file).map_err(|e| format!("Could not read '{}': {}", file, e))?;

    let turn_json: serde_json::Value =
        serde_json::from_str(&content).map_err(|e| format!("Invalid JSON in '{}': {}", file, e))?;

    let spinner = ctx.spinner("Submitting turn...");
    let data = post_json(cfg, "/turn/submit", &turn_json).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let turn_id = data["turn_id"].as_str().unwrap_or("?");
    let status_str = data["status"].as_str().unwrap_or("submitted");
    ctx.success(&format!("Turn submitted: {}", abbrev_hex(turn_id, 8, 4)));
    ctx.kv("Status", status_str);
    ctx.info("  Check progress with: pyana turn status <turn-id>");

    Ok(())
}

async fn status(
    cfg: &Config,
    ctx: &Context,
    turn_id: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner("Checking turn status...");
    // Try to get from receipts endpoint.
    let data = get_json(cfg, "/wallet/receipts").await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    // Find the matching receipt.
    let receipts = data.as_array();
    let found = receipts.and_then(|rs| rs.iter().find(|r| r["turn_id"].as_str() == Some(turn_id)));

    match found {
        Some(receipt) => {
            let status_str = receipt["status"].as_str().unwrap_or("unknown");
            let height = receipt["height"].as_u64().unwrap_or(0);
            let computrons = receipt["computrons_used"].as_u64().unwrap_or(0);

            ctx.header("Turn Receipt");
            ctx.kv("Turn ID", &abbrev_hex(turn_id, 8, 4));
            ctx.kv("Status", status_str);
            ctx.kv("Height", &height.to_string());
            ctx.kv("Computrons", &crate::output::format_number(computrons));
        }
        None => {
            ctx.warn(&format!(
                "No receipt found for turn {}",
                abbrev_hex(turn_id, 8, 4)
            ));
            ctx.info("  The turn may still be pending, or the ID may be incorrect.");
        }
    }

    Ok(())
}

async fn build(cfg: &Config, ctx: &Context) -> Result<(), Box<dyn std::error::Error>> {
    ctx.header("Interactive Turn Builder");
    ctx.info("Build a turn step by step.\n");

    // Step 1: Select target cell.
    let cell_id: String = Input::new().with_prompt("Target cell ID").interact_text()?;

    // Step 2: Select effect type (all 18 effect types including CapTP).
    let effect_types = &[
        "Transfer",
        "SetField",
        "CreateCell",
        "Invoke",
        "DeployProgram",
        "DeleteCell",
        "Delegate",
        "Revoke",
        "Emit",
        "Subscribe",
        "Unsubscribe",
        "Spawn",
        "Upgrade",
        "Checkpoint",
        // CapTP effects:
        "ExportSturdyRef",
        "EnlivenRef",
        "DropRef",
        "ValidateHandoff",
    ];
    let effect_idx = Select::new()
        .with_prompt("Effect type")
        .items(effect_types)
        .default(0)
        .interact()?;

    let effect_type = effect_types[effect_idx];

    // Step 3: Build the effect based on type.
    let effect = match effect_type {
        "Transfer" => {
            let recipient: String = Input::new()
                .with_prompt("Recipient cell ID")
                .interact_text()?;
            let amount: String = Input::new()
                .with_prompt("Amount (computrons)")
                .interact_text()?;
            serde_json::json!({
                "type": "Transfer",
                "recipient": recipient,
                "amount": amount.parse::<u64>().unwrap_or(0),
            })
        }
        "SetField" => {
            let field: String = Input::new().with_prompt("Field name").interact_text()?;
            let value: String = Input::new().with_prompt("Value (JSON)").interact_text()?;
            let parsed_value: serde_json::Value =
                serde_json::from_str(&value).unwrap_or(serde_json::Value::String(value));
            serde_json::json!({
                "type": "SetField",
                "field": field,
                "value": parsed_value,
            })
        }
        "CreateCell" => {
            let program: String = Input::new()
                .with_prompt("Program ID (empty for bare cell)")
                .allow_empty(true)
                .interact_text()?;
            serde_json::json!({
                "type": "CreateCell",
                "program": program,
            })
        }
        "Invoke" => {
            let method: String = Input::new().with_prompt("Method name").interact_text()?;
            let args: String = Input::new()
                .with_prompt("Arguments (JSON array)")
                .default("[]".to_string())
                .interact_text()?;
            let parsed_args: serde_json::Value =
                serde_json::from_str(&args).unwrap_or(serde_json::json!([]));
            serde_json::json!({
                "type": "Invoke",
                "method": method,
                "args": parsed_args,
            })
        }
        "DeployProgram" => {
            let name: String = Input::new().with_prompt("Program name").interact_text()?;
            let bytecode_path: String = Input::new()
                .with_prompt("Bytecode file path")
                .interact_text()?;
            serde_json::json!({
                "type": "DeployProgram",
                "name": name,
                "bytecode_path": bytecode_path,
            })
        }
        "DeleteCell" => {
            let target: String = Input::new()
                .with_prompt("Cell ID to delete")
                .interact_text()?;
            serde_json::json!({
                "type": "DeleteCell",
                "target": target,
            })
        }
        "Delegate" => {
            let target: String = Input::new()
                .with_prompt("Delegate to (cell ID or public key)")
                .interact_text()?;
            let attenuate: String = Input::new()
                .with_prompt("Attenuation (empty for full)")
                .allow_empty(true)
                .interact_text()?;
            serde_json::json!({
                "type": "Delegate",
                "target": target,
                "attenuation": if attenuate.is_empty() { serde_json::Value::Null } else { serde_json::Value::String(attenuate) },
            })
        }
        "Revoke" => {
            let token_id: String = Input::new()
                .with_prompt("Token/capability ID to revoke")
                .interact_text()?;
            serde_json::json!({
                "type": "Revoke",
                "token_id": token_id,
            })
        }
        "Emit" => {
            let event_type: String = Input::new().with_prompt("Event type").interact_text()?;
            let payload: String = Input::new()
                .with_prompt("Payload (JSON)")
                .default("{}".to_string())
                .interact_text()?;
            let parsed_payload: serde_json::Value =
                serde_json::from_str(&payload).unwrap_or(serde_json::json!({}));
            serde_json::json!({
                "type": "Emit",
                "event_type": event_type,
                "payload": parsed_payload,
            })
        }
        "Subscribe" => {
            let source_cell: String = Input::new()
                .with_prompt("Source cell ID to subscribe to")
                .interact_text()?;
            let event_filter: String = Input::new()
                .with_prompt("Event filter (empty for all)")
                .allow_empty(true)
                .interact_text()?;
            serde_json::json!({
                "type": "Subscribe",
                "source_cell": source_cell,
                "event_filter": if event_filter.is_empty() { serde_json::Value::Null } else { serde_json::Value::String(event_filter) },
            })
        }
        "Unsubscribe" => {
            let subscription_id: String = Input::new()
                .with_prompt("Subscription ID")
                .interact_text()?;
            serde_json::json!({
                "type": "Unsubscribe",
                "subscription_id": subscription_id,
            })
        }
        "Spawn" => {
            let program: String = Input::new()
                .with_prompt("Program ID for spawned cell")
                .interact_text()?;
            let init_args: String = Input::new()
                .with_prompt("Init arguments (JSON)")
                .default("{}".to_string())
                .interact_text()?;
            let parsed_init: serde_json::Value =
                serde_json::from_str(&init_args).unwrap_or(serde_json::json!({}));
            serde_json::json!({
                "type": "Spawn",
                "program": program,
                "init_args": parsed_init,
            })
        }
        "Upgrade" => {
            let new_program: String = Input::new().with_prompt("New program ID").interact_text()?;
            let migration: String = Input::new()
                .with_prompt("Migration function (empty for default)")
                .allow_empty(true)
                .interact_text()?;
            serde_json::json!({
                "type": "Upgrade",
                "new_program": new_program,
                "migration": if migration.is_empty() { serde_json::Value::Null } else { serde_json::Value::String(migration) },
            })
        }
        "Checkpoint" => {
            let label: String = Input::new()
                .with_prompt("Checkpoint label (empty for auto)")
                .allow_empty(true)
                .interact_text()?;
            serde_json::json!({
                "type": "Checkpoint",
                "label": if label.is_empty() { serde_json::Value::Null } else { serde_json::Value::String(label) },
            })
        }
        // CapTP effects:
        "ExportSturdyRef" => {
            let target_cell: String = Input::new()
                .with_prompt("Cell ID to export")
                .interact_text()?;
            let attenuation: String = Input::new()
                .with_prompt("Attenuation (empty for full)")
                .allow_empty(true)
                .interact_text()?;
            serde_json::json!({
                "type": "ExportSturdyRef",
                "target_cell": target_cell,
                "attenuation": if attenuation.is_empty() { serde_json::Value::Null } else { serde_json::Value::String(attenuation) },
            })
        }
        "EnlivenRef" => {
            let uri: String = Input::new()
                .with_prompt("Sturdy reference URI (pyana://...)")
                .interact_text()?;
            serde_json::json!({
                "type": "EnlivenRef",
                "uri": uri,
            })
        }
        "DropRef" => {
            let ref_id: String = Input::new()
                .with_prompt("Reference ID to drop")
                .interact_text()?;
            serde_json::json!({
                "type": "DropRef",
                "ref_id": ref_id,
            })
        }
        "ValidateHandoff" => {
            let certificate: String = Input::new()
                .with_prompt("Handoff certificate (hex)")
                .interact_text()?;
            let recipient_pk: String = Input::new()
                .with_prompt("Recipient public key (hex)")
                .interact_text()?;
            serde_json::json!({
                "type": "ValidateHandoff",
                "certificate": certificate,
                "recipient_pk": recipient_pk,
            })
        }
        _ => serde_json::json!({}),
    };

    // Step 4: Assemble turn.
    let turn = serde_json::json!({
        "cell_id": cell_id,
        "effects": [effect],
    });

    eprintln!();
    ctx.info("Constructed turn:");
    eprintln!("{}", serde_json::to_string_pretty(&turn)?);
    eprintln!();

    // Step 5: Confirm and submit.
    let submit_choices = &["Submit now", "Save to file", "Cancel"];
    let choice = Select::new()
        .with_prompt("Action")
        .items(submit_choices)
        .default(0)
        .interact()?;

    match choice {
        0 => {
            let spinner = ctx.spinner("Submitting turn...");
            let data = post_json(cfg, "/turn/submit", &turn).await?;
            spinner.finish_and_clear();

            if cfg.is_json() {
                ctx.json_stdout(&data);
            } else {
                let turn_id = data["turn_id"].as_str().unwrap_or("?");
                ctx.success(&format!("Turn submitted: {}", turn_id));
            }
        }
        1 => {
            let filename: String = Input::new()
                .with_prompt("Output file path")
                .default("turn.json".to_string())
                .interact_text()?;
            std::fs::write(&filename, serde_json::to_string_pretty(&turn)?)?;
            ctx.success(&format!("Saved to {filename}"));
        }
        _ => {
            ctx.info("Cancelled.");
        }
    }

    Ok(())
}
