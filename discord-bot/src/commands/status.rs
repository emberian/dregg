//! `/status`, `/proof verify`, `/metrics` commands — federation health and verification.

use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, CreateInteractionResponse, CreateInteractionResponseMessage,
    EditInteractionResponse,
};

use crate::BotState;
use crate::embeds;

/// Register the /status command.
pub fn register_status() -> CreateCommand {
    CreateCommand::new("status").description("Show federation health status")
}

/// Register the /proof command (for proof verification).
pub fn register_proof() -> CreateCommand {
    CreateCommand::new("proof")
        .description("Verify a STARK proof")
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "verify",
                "Verify a STARK proof by hex",
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "hex",
                    "Hex-encoded STARK proof",
                )
                .required(true),
            ),
        )
}

/// Register the /metrics command.
pub fn register_metrics() -> CreateCommand {
    CreateCommand::new("metrics").description("Show key devnet metrics")
}

/// Handle /status interaction.
pub async fn handle_status(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer_ephemeral(ctx, command).await;

    match state.devnet.federation_health().await {
        Ok(health) => {
            let status_icon = match health.status.as_str() {
                "healthy" => "\u{2705}",
                "degraded" => "\u{26a0}\u{fe0f}",
                _ => "\u{274c}",
            };

            let embed = embeds::pyana_embed("Federation Status")
                .field(
                    "Status",
                    format!("{status_icon} {}", health.status.to_uppercase()),
                    true,
                )
                .field(
                    "Nodes",
                    format!("{}/{}", health.nodes_up, health.nodes_total),
                    true,
                )
                .field("Block Height", health.block_height.to_string(), true)
                .field("Last Block", &health.last_block_time, true)
                .field(
                    "Avg Block Time",
                    format!("{}ms", health.avg_block_time_ms),
                    true,
                );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed(
                "Federation Offline",
                &format!(
                    "Could not reach the federation: {e}\n\nDevnet is currently offline, try again later."
                ),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

/// Handle /proof interaction.
pub async fn handle_proof(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let sub_opts = match &command.data.options[0].value {
        CommandDataOptionValue::SubCommand(opts) => opts.clone(),
        _ => return,
    };

    let proof_hex = sub_opts
        .iter()
        .find(|o| o.name == "hex")
        .and_then(|o| match &o.value {
            CommandDataOptionValue::String(s) => Some(s.clone()),
            _ => None,
        })
        .unwrap_or_default();

    defer_ephemeral(ctx, command).await;

    match state.devnet.verify_proof(&proof_hex).await {
        Ok(result) => {
            let valid_icon = if result.valid { "\u{2705}" } else { "\u{274c}" };

            let mut embed = embeds::pyana_embed("Proof Verification").field(
                "Valid",
                format!("{valid_icon} {}", result.valid),
                true,
            );

            if let Some(air) = &result.air_name {
                embed = embed.field("AIR", air, true);
            }

            if let Some(inputs) = &result.public_inputs {
                let inputs_str = inputs
                    .iter()
                    .take(5)
                    .map(|i| format!("`{}`", i))
                    .collect::<Vec<_>>()
                    .join(", ");
                embed = embed.field("Public Inputs", inputs_str, false);
            }

            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed(
                "Verification Failed",
                &format!(
                    "Could not verify proof: {e}\n\nEnsure the hex is valid and devnet is online."
                ),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

/// Handle /metrics interaction.
pub async fn handle_metrics(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer_ephemeral(ctx, command).await;

    match state.devnet.metrics().await {
        Ok(metrics) => {
            let uptime_str = format_uptime(metrics.uptime_secs);

            let embed = embeds::pyana_embed("Devnet Metrics")
                .field("TPS", format!("{:.2}", metrics.tps), true)
                .field("Block Height", metrics.block_height.to_string(), true)
                .field("Pending Turns", metrics.pending_turns.to_string(), true)
                .field("Active Cells", metrics.active_cells.to_string(), true)
                .field("Memory", format!("{} MB", metrics.memory_usage_mb), true)
                .field("Uptime", uptime_str, true);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed(
                "Metrics Unavailable",
                &format!(
                    "Could not load metrics: {e}\n\nDevnet is currently offline, try again later."
                ),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

fn format_uptime(secs: u64) -> String {
    let days = secs / 86400;
    let hours = (secs % 86400) / 3600;
    let mins = (secs % 3600) / 60;
    if days > 0 {
        format!("{days}d {hours}h {mins}m")
    } else if hours > 0 {
        format!("{hours}h {mins}m")
    } else {
        format!("{mins}m")
    }
}

// ─── Helpers ────────────────────────────────────────────────────────────────

async fn defer_ephemeral(ctx: &Context, command: &CommandInteraction) {
    let _ = command
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Defer(
                CreateInteractionResponseMessage::new().ephemeral(true),
            ),
        )
        .await;
}
