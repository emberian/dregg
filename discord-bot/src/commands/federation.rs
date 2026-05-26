//! Federation setup commands: `/setup-federation`, `/link-cipherclerk`, `/unlink-cipherclerk`.
//!
//! Links a Discord guild to a dregg reference group and binds user identities.

use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, CreateInteractionResponse, CreateInteractionResponseMessage,
    EditInteractionResponse,
};

use crate::BotState;
use crate::embeds;

// ─── Registration ───────────────────────────────────────────────────────────

/// Register `/setup-federation`.
pub fn register_setup() -> CreateCommand {
    CreateCommand::new("setup-federation")
        .description("Register this guild as a dregg reference group (federation)")
}

/// Register `/link-cipherclerk <dregg-address>`.
pub fn register_link() -> CreateCommand {
    CreateCommand::new("link-cipherclerk")
        .description("Link your Discord account to your dregg identity")
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::String,
                "address",
                "Your dregg cell address (hex)",
            )
            .required(true),
        )
}

/// Register `/unlink-cipherclerk`.
pub fn register_unlink() -> CreateCommand {
    CreateCommand::new("unlink-cipherclerk")
        .description("Unlink your Discord account from your dregg identity")
}

// ─── Handlers ───────────────────────────────────────────────────────────────

/// Handle `/setup-federation`.
pub async fn handle_setup(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let guild_id = match command.guild_id {
        Some(id) => id.get(),
        None => {
            respond_error(
                ctx,
                command,
                "Guild Required",
                "This command must be run in a server.",
            )
            .await;
            return;
        }
    };

    // Check that the user has admin permissions.
    let member = match &command.member {
        Some(m) => m,
        None => {
            respond_error(
                ctx,
                command,
                "Permission Denied",
                "Cannot determine your server permissions.",
            )
            .await;
            return;
        }
    };

    let has_admin = member
        .permissions
        .map(|p| p.administrator())
        .unwrap_or(false);

    if !has_admin {
        respond_error(
            ctx,
            command,
            "Permission Denied",
            "Only server administrators can set up federation.",
        )
        .await;
        return;
    }

    defer_ephemeral(ctx, command).await;

    let url = format!("{}/federation/register-guild", state.config.devnet_url);
    let body = serde_json::json!({
        "guild_id": guild_id,
        "bot_cell": state.captp.bot_cell_id,
        "guild_name": command.guild_id.map(|g| g.get().to_string()).unwrap_or_default(),
    });

    let resp = state.devnet.client().post(&url).json(&body).send().await;

    match resp {
        Ok(r) if r.status().is_success() => {
            let result: SetupResponse = match r.json().await {
                Ok(s) => s,
                Err(e) => {
                    let embed = embeds::error_embed("Parse Error", &e.to_string());
                    let _ = command
                        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                        .await;
                    return;
                }
            };

            let embed = embeds::success_embed("Federation Registered")
                .description("This guild is now a dregg reference group.")
                .field("Federation ID", format!("`{}`", result.federation_id), true)
                .field("Namespace", format!("`/discord/{guild_id}/`"), true)
                .field(
                    "Bot Cell",
                    format!(
                        "`{}...`",
                        &state.captp.bot_cell_id[..16.min(state.captp.bot_cell_id.len())]
                    ),
                    true,
                );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Ok(r) => {
            let body = r.text().await.unwrap_or_default();
            let embed = embeds::error_embed("Setup Failed", &body);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Node Unreachable", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

/// Handle `/link-cipherclerk`.
pub async fn handle_link(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let address = command
        .data
        .options
        .first()
        .and_then(|o| match &o.value {
            CommandDataOptionValue::String(s) => Some(s.clone()),
            _ => None,
        })
        .unwrap_or_default();

    defer_ephemeral(ctx, command).await;

    let discord_id = command.user.id.get().to_string();

    // Validate the address format (should be hex, 64 chars = 32 bytes).
    if address.len() != 64 || hex::decode(&address).is_err() {
        let embed = embeds::error_embed(
            "Invalid Address",
            "Dregg cell address must be 64 hex characters (32 bytes).",
        );
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    }

    // Check if already linked.
    match state.db.get_cell_id(&discord_id).await {
        Ok(Some(existing)) => {
            let embed = embeds::warning_embed(
                "Already Linked",
                &format!(
                    "Your account is already linked to `{}...`.\nUse `/unlink-cipherclerk` first to change it.",
                    &existing[..16.min(existing.len())]
                ),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
        Err(e) => {
            let embed = embeds::error_embed("Database Error", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
        _ => {}
    }

    let challenge = ownership_challenge(&discord_id, &address);

    // Store as pending only. A later verifier can promote this record after a
    // signature proof over the challenge; until then the bot will not sign for it.
    match state
        .db
        .create_pending_external_link(&discord_id, &address, &challenge)
        .await
    {
        Ok(()) => {
            let embed = embeds::success_embed("External Link Pending")
                .description("Your Discord account recorded this external identity, but it is not active until ownership is proven.")
                .field("Cell ID", format!("`{}...`", &address[..16]), true)
                .field("Challenge", format!("```\n{challenge}\n```"), false);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Link Failed", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

/// Handle `/unlink-cipherclerk`.
pub async fn handle_unlink(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer_ephemeral(ctx, command).await;

    let discord_id = command.user.id.get().to_string();

    match state.db.get_cell_id(&discord_id).await {
        Ok(Some(_)) => match state.db.unlink_user(&discord_id).await {
            Ok(()) => {
                let embed = embeds::success_embed("Cipherclerk Unlinked").description(
                    "Your Discord account has been unlinked from your dregg identity.",
                );
                let _ = command
                    .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                    .await;
            }
            Err(e) => {
                let embed = embeds::error_embed("Unlink Failed", &e.to_string());
                let _ = command
                    .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                    .await;
            }
        },
        Ok(None) => {
            let embed = embeds::warning_embed(
                "Not Linked",
                "Your Discord account is not linked to any dregg identity.",
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Database Error", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

fn ownership_challenge(discord_id: &str, address: &str) -> String {
    let input = format!("dregg-discord-link-v1:{discord_id}:{address}");
    format!(
        "dregg-discord-link-v1:{}",
        blake3::hash(input.as_bytes()).to_hex()
    )
}

// ─── Wire types ─────────────────────────────────────────────────────────────

#[derive(serde::Deserialize)]
struct SetupResponse {
    federation_id: String,
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

async fn respond_error(ctx: &Context, command: &CommandInteraction, title: &str, desc: &str) {
    let embed = embeds::error_embed(title, desc);
    let msg = CreateInteractionResponseMessage::new()
        .embed(embed)
        .ephemeral(true);
    let _ = command
        .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
        .await;
}
