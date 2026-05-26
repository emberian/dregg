//! CapTP slash commands: `/cap-share`, `/cap-accept`, `/cap-delegate`, `/cap-list`, `/cap-revoke`.
//!
//! The bot acts as a capability peer — it can export, enliven, delegate, and revoke
//! sturdy references on behalf of Discord users.

use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, CreateInteractionResponse, CreateInteractionResponseMessage,
    EditInteractionResponse,
};

use crate::BotState;
use crate::db::IdentityMode;
use crate::embeds;

// ─── Registration ───────────────────────────────────────────────────────────

/// Register `/cap-share <cell-id>`.
pub fn register_share() -> CreateCommand {
    CreateCommand::new("cap-share")
        .description("Export a sturdy ref and share it as an embed")
        .add_option(
            CreateCommandOption::new(CommandOptionType::String, "cell-id", "Cell ID to export")
                .required(true),
        )
}

/// Register `/cap-accept <dregg-uri>`.
pub fn register_accept() -> CreateCommand {
    CreateCommand::new("cap-accept")
        .description("Enliven a shared dregg URI — bot holds the live ref")
        .add_option(
            CreateCommandOption::new(CommandOptionType::String, "uri", "dregg:// URI to enliven")
                .required(true),
        )
}

/// Register `/cap-delegate <cell> <@user>`.
pub fn register_delegate() -> CreateCommand {
    CreateCommand::new("cap-delegate")
        .description("Create a handoff cert for a Discord user")
        .add_option(
            CreateCommandOption::new(CommandOptionType::String, "cell-id", "Cell ID to delegate")
                .required(true),
        )
        .add_option(
            CreateCommandOption::new(CommandOptionType::User, "user", "User to delegate to")
                .required(true),
        )
}

/// Register `/cap-list`.
pub fn register_list() -> CreateCommand {
    CreateCommand::new("cap-list").description("Show the bot's held capabilities")
}

/// Register `/cap-revoke <cell-id>`.
pub fn register_revoke() -> CreateCommand {
    CreateCommand::new("cap-revoke")
        .description("Revoke a previously shared capability")
        .add_option(
            CreateCommandOption::new(CommandOptionType::String, "cell-id", "Cell ID to revoke")
                .required(true),
        )
}

// ─── Handlers ───────────────────────────────────────────────────────────────

/// Handle `/cap-share`.
pub async fn handle_share(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let cell_id = command
        .data
        .options
        .first()
        .and_then(|o| match &o.value {
            CommandDataOptionValue::String(s) => Some(s.clone()),
            _ => None,
        })
        .unwrap_or_default();

    defer_ephemeral(ctx, command).await;

    if let Err(embed) = ensure_user_can_manage_cell(command, state, &cell_id).await {
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    }

    match state.captp.export_cap(&cell_id).await {
        Ok(uri) => {
            let uri_str = uri.to_string();
            let short_cell = if cell_id.len() > 16 {
                format!("{}...", &cell_id[..16])
            } else {
                cell_id.clone()
            };

            let embed = embeds::success_embed("Capability Shared")
                .description("Sturdy ref exported. Anyone with this URI can enliven the cap.")
                .field("Cell", format!("`{short_cell}`"), true)
                .field("URI", format!("```\n{uri_str}\n```"), false);

            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Export Failed", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

/// Handle `/cap-accept`.
pub async fn handle_accept(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let uri = command
        .data
        .options
        .first()
        .and_then(|o| match &o.value {
            CommandDataOptionValue::String(s) => Some(s.clone()),
            _ => None,
        })
        .unwrap_or_default();

    defer_ephemeral(ctx, command).await;

    match state.captp.accept_cap(&uri).await {
        Ok(cap) => {
            let cell_id = hex::encode(cap.uri.cell_id);
            let short = if cell_id.len() > 16 {
                format!("{}...", &cell_id[..16])
            } else {
                cell_id.clone()
            };

            let embed = embeds::success_embed("Capability Accepted")
                .description("The bot now holds this live reference.")
                .field("Cell", format!("`{short}`"), true)
                .field("Status", "Live", true);

            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Accept Failed", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

/// Handle `/cap-delegate`.
pub async fn handle_delegate(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let cell_id = command
        .data
        .options
        .iter()
        .find(|o| o.name == "cell-id")
        .and_then(|o| match &o.value {
            CommandDataOptionValue::String(s) => Some(s.clone()),
            _ => None,
        })
        .unwrap_or_default();

    let target_user_id = command
        .data
        .options
        .iter()
        .find(|o| o.name == "user")
        .and_then(|o| match &o.value {
            CommandDataOptionValue::User(uid) => Some(uid.get()),
            _ => None,
        });

    defer_ephemeral(ctx, command).await;

    if let Err(embed) = ensure_user_can_manage_cell(command, state, &cell_id).await {
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    }

    let target_id = match target_user_id {
        Some(id) => id,
        None => {
            let embed = embeds::error_embed("Invalid Arguments", "Please specify a target user.");
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
    };

    // Look up the target user's dregg key.
    let target_discord = target_id.to_string();
    let recipient_key = match state.db.get_user_identity(&target_discord).await {
        Ok(Some(identity)) if identity.mode != IdentityMode::ExternalPending => identity.cell_id,
        Ok(Some(_)) => {
            let embed = embeds::warning_embed(
                "Target Link Pending",
                &format!(
                    "<@{target_id}> has a pending external identity link. They need to prove ownership before receiving delegated capabilities."
                ),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
        Ok(None) => {
            let embed = embeds::warning_embed(
                "Target Has No Cipherclerk",
                &format!("<@{target_id}> does not have a linked dregg identity."),
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
    };

    match state.captp.delegate_cap(&cell_id, &recipient_key).await {
        Ok(cert) => {
            let short_cert = if cert.len() > 64 {
                format!("{}...", &cert[..64])
            } else {
                cert.clone()
            };

            let embed = embeds::success_embed("Capability Delegated")
                .description(format!("Handoff certificate created for <@{target_id}>."))
                .field("Cell", format!("`{}`", &cell_id), true)
                .field("Certificate", format!("```\n{short_cert}\n```"), false);

            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Delegation Failed", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

/// Handle `/cap-list`.
pub async fn handle_list(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer_ephemeral(ctx, command).await;

    let held = state.captp.list_held().await;
    let exports = state.captp.list_exports().await;

    if held.is_empty() && exports.is_empty() {
        let embed = embeds::dregg_embed("Bot Capabilities")
            .description("No capabilities currently held or exported.");
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    }

    let mut desc = String::new();

    if !held.is_empty() {
        desc.push_str("**Held (live refs):**\n");
        for (cell_id, cap) in &held {
            let short = if cell_id.len() > 16 {
                format!("{}...", &cell_id[..16])
            } else {
                cell_id.clone()
            };
            let label = cap.label.as_deref().unwrap_or("unlabeled");
            let status = if cap.live { "live" } else { "stale" };
            desc.push_str(&format!("- `{short}` ({label}) [{status}]\n"));
        }
        desc.push('\n');
    }

    if !exports.is_empty() {
        desc.push_str("**Exported (shared):**\n");
        for (cell_id, export) in &exports {
            let short = if cell_id.len() > 16 {
                format!("{}...", &cell_id[..16])
            } else {
                cell_id.clone()
            };
            let status = if export.revoked { "revoked" } else { "active" };
            desc.push_str(&format!("- `{short}` [{status}]\n"));
        }
    }

    let embed = embeds::dregg_embed("Bot Capabilities")
        .description(desc)
        .field("Held", held.len().to_string(), true)
        .field("Exported", exports.len().to_string(), true);

    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
}

/// Handle `/cap-revoke`.
pub async fn handle_revoke(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let cell_id = command
        .data
        .options
        .first()
        .and_then(|o| match &o.value {
            CommandDataOptionValue::String(s) => Some(s.clone()),
            _ => None,
        })
        .unwrap_or_default();

    defer_ephemeral(ctx, command).await;

    if let Err(embed) = ensure_user_can_manage_cell(command, state, &cell_id).await {
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    }

    match state.captp.revoke_cap(&cell_id).await {
        Ok(()) => {
            let embed = embeds::success_embed("Capability Revoked").description(format!(
                "Cell `{}` has been revoked. The sturdy ref is no longer valid.",
                &cell_id
            ));
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Revoke Failed", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
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

async fn ensure_user_can_manage_cell(
    command: &CommandInteraction,
    state: &BotState,
    cell_id: &str,
) -> Result<(), serenity::all::CreateEmbed> {
    if cell_id.len() != 64 || hex::decode(cell_id).is_err() {
        return Err(embeds::error_embed(
            "Invalid Cell ID",
            "Cell IDs must be 64 hex characters.",
        ));
    }

    let discord_id = command.user.id.get().to_string();
    match state.db.get_user_identity(&discord_id).await {
        Ok(Some(identity))
            if identity.mode == IdentityMode::Hosted && identity.cell_id == cell_id =>
        {
            Ok(())
        }
        Ok(Some(identity)) if identity.cell_id == cell_id => Err(embeds::warning_embed(
            "External Identity Pending",
            "The bot cannot export, delegate, or revoke capabilities for an external identity until holder proof is implemented and verified.",
        )),
        Ok(Some(_)) => Err(embeds::error_embed(
            "Capability Not Held",
            "You can only manage capabilities for your own hosted cipherclerk cell.",
        )),
        Ok(None) => Err(embeds::warning_embed(
            "No Cipherclerk",
            "Create a hosted cipherclerk with `/cipherclerk create` before managing capabilities.",
        )),
        Err(e) => Err(embeds::error_embed("Database Error", &e.to_string())),
    }
}
