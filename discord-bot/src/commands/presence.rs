//! `/presence` commands — status, attest, verify, history.

use serenity::all::{
    CommandInteraction, CommandOptionType, Context, CreateCommand, CreateCommandOption,
    CreateInteractionResponse, CreateInteractionResponseMessage, EditInteractionResponse,
};

use crate::BotState;
use crate::cipherclerk::UserCipherclerk;
use crate::embeds;
use crate::presence::{PresenceAttestation, PresenceClaim};

/// Register the /presence command.
pub fn register() -> CreateCommand {
    CreateCommand::new("presence")
        .description("Presence attestation system — prove you are online")
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "status",
            "Show your current presence record",
        ))
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "attest",
                "Request a signed presence attestation",
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "claim",
                    "Claim type: currently_online, online_for:<secs>, online_within:<secs>",
                )
                .required(false),
            ),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "verify",
                "Verify a presence attestation",
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "attestation",
                    "Hex-encoded attestation to verify",
                )
                .required(true),
            ),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "history",
                "Show presence history for a user (last 24h)",
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::User,
                    "user",
                    "User to check (default: yourself)",
                )
                .required(false),
            ),
        )
}

/// Handle /presence interactions.
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let subcommand = &command.data.options[0].name;

    match subcommand.as_str() {
        "status" => handle_status(ctx, command, state).await,
        "attest" => handle_attest(ctx, command, state).await,
        "verify" => handle_verify(ctx, command, state).await,
        "history" => handle_history(ctx, command, state).await,
        _ => {}
    }
}

async fn handle_status(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let user_id = command.user.id.get();

    let tracker = state.presence.lock().await;
    let embed = match tracker.get_snapshot(user_id) {
        Some(record) => {
            let duration_str = format_duration(record.online_duration_secs);
            let last_online_str = record
                .last_online
                .map(|ts| format!("<t:{ts}:R>"))
                .unwrap_or_else(|| "Never seen".to_string());

            embeds::pyana_embed("Presence Status")
                .field("Status", record.status.to_string(), true)
                .field("Session Duration", duration_str, true)
                .field("Last Online", last_online_str, true)
        }
        None => embeds::warning_embed(
            "No Presence Data",
            "The bot has not observed any presence updates for you yet.",
        ),
    };

    respond_ephemeral(ctx, command, embed).await;
}

async fn handle_attest(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let user_id = command.user.id.get();

    // Parse the claim type from options.
    let claim = parse_claim_from_options(command).unwrap_or(PresenceClaim::CurrentlyOnline);

    // Get the user's cell ID via the canonical AppCipherclerk.
    let cclerk =
        UserCipherclerk::derive(&state.config.bot_secret, user_id, state.federation_id_bytes);

    let _ = command
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Defer(
                CreateInteractionResponseMessage::new().ephemeral(true),
            ),
        )
        .await;

    let result = {
        let mut tracker = state.presence.lock().await;
        tracker.attest(user_id, cclerk.cell_id_bytes(), claim.clone())
    };

    match result {
        Ok(attestation) => {
            let hex_str = attestation.to_hex();
            let short_sig = &hex::encode(attestation.signature)[..16];

            let embed = embeds::success_embed("Presence Attestation Issued")
                .field("Claim", claim.to_string(), true)
                .field("Expires", format!("<t:{}:R>", attestation.expires_at), true)
                .field("Signature", format!("`{short_sig}...`"), true)
                .field("Attestation (hex)", format!("```\n{hex_str}\n```"), false);

            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Attestation Failed", &e);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

async fn handle_verify(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let sub_opts = &command.data.options[0];
    let options = match &sub_opts.value {
        serenity::all::CommandDataOptionValue::SubCommand(opts) => opts,
        _ => return,
    };

    let mut attestation_hex = String::new();
    for opt in options {
        if opt.name == "attestation" {
            if let serenity::all::CommandDataOptionValue::String(s) = &opt.value {
                attestation_hex = s.clone();
            }
        }
    }

    let embed = match PresenceAttestation::from_hex(&attestation_hex) {
        Some(attestation) => {
            let tracker = state.presence.lock().await;
            let valid = tracker.verify_attestation(&attestation);

            let now = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_secs() as i64;
            let expired = attestation.expires_at < now;

            if valid && !expired {
                embeds::success_embed("Attestation Valid")
                    .field("User", format!("<@{}>", attestation.user_id), true)
                    .field("Claim", attestation.claim.to_string(), true)
                    .field("Expires", format!("<t:{}:R>", attestation.expires_at), true)
            } else if valid && expired {
                embeds::warning_embed(
                    "Attestation Expired",
                    &format!(
                        "Signature is valid but attestation expired <t:{}:R>.",
                        attestation.expires_at
                    ),
                )
            } else {
                embeds::error_embed(
                    "Invalid Attestation",
                    "Signature verification failed. This attestation is forged or corrupted.",
                )
            }
        }
        None => embeds::error_embed(
            "Parse Error",
            "Could not decode attestation. Ensure it is valid hex.",
        ),
    };

    respond_ephemeral(ctx, command, embed).await;
}

async fn handle_history(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let sub_opts = &command.data.options[0];
    let options = match &sub_opts.value {
        serenity::all::CommandDataOptionValue::SubCommand(opts) => opts,
        _ => return,
    };

    let mut target_user_id = command.user.id.get();
    for opt in options {
        if opt.name == "user" {
            if let serenity::all::CommandDataOptionValue::User(uid) = &opt.value {
                target_user_id = uid.get();
            }
        }
    }

    let tracker = state.presence.lock().await;
    let history = tracker.history(target_user_id, 86400); // last 24h

    let embed = if history.is_empty() {
        embeds::pyana_embed("Presence History").description(format!(
            "No presence changes recorded for <@{target_user_id}> in the last 24h."
        ))
    } else {
        let entries: Vec<String> = history
            .iter()
            .rev()
            .take(20)
            .map(|e| {
                let label = match e.status {
                    crate::presence::PresenceStatus::Online => "Online",
                    crate::presence::PresenceStatus::Idle => "Idle",
                    crate::presence::PresenceStatus::Dnd => "DnD",
                    crate::presence::PresenceStatus::Offline => "Offline",
                };
                format!("<t:{}:t> {}", e.timestamp, label)
            })
            .collect();

        embeds::pyana_embed("Presence History").description(format!(
            "Last 24h for <@{target_user_id}> ({} events):\n{}",
            history.len(),
            entries.join("\n")
        ))
    };

    respond_ephemeral(ctx, command, embed).await;
}

/// Parse a PresenceClaim from command options.
fn parse_claim_from_options(command: &CommandInteraction) -> Option<PresenceClaim> {
    let sub_opts = &command.data.options[0];
    let options = match &sub_opts.value {
        serenity::all::CommandDataOptionValue::SubCommand(opts) => opts,
        _ => return None,
    };

    for opt in options {
        if opt.name == "claim" {
            if let serenity::all::CommandDataOptionValue::String(s) = &opt.value {
                return parse_claim_string(s);
            }
        }
    }
    None
}

/// Parse a claim string like "currently_online", "online_for:3600", "online_within:600".
fn parse_claim_string(s: &str) -> Option<PresenceClaim> {
    let s = s.trim().to_lowercase();
    if s == "currently_online" || s == "online" {
        return Some(PresenceClaim::CurrentlyOnline);
    }
    if let Some(rest) = s.strip_prefix("online_for:") {
        let secs: u64 = rest.trim().parse().ok()?;
        return Some(PresenceClaim::OnlineForAtLeast {
            duration_secs: secs,
        });
    }
    if let Some(rest) = s.strip_prefix("online_within:") {
        let secs: u64 = rest.trim().parse().ok()?;
        return Some(PresenceClaim::OnlineWithin { window_secs: secs });
    }
    None
}

fn format_duration(secs: u64) -> String {
    if secs < 60 {
        format!("{secs}s")
    } else if secs < 3600 {
        format!("{}m {}s", secs / 60, secs % 60)
    } else {
        format!("{}h {}m", secs / 3600, (secs % 3600) / 60)
    }
}

async fn respond_ephemeral(
    ctx: &Context,
    command: &CommandInteraction,
    embed: serenity::all::CreateEmbed,
) {
    let msg = CreateInteractionResponseMessage::new()
        .embed(embed)
        .ephemeral(true);
    let _ = command
        .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
        .await;
}
