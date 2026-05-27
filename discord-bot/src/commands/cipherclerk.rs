//! `/cipherclerk` command — create, balance, address, export.

use serenity::all::{
    CommandInteraction, CommandOptionType, Context, CreateCommand, CreateCommandOption,
    CreateInteractionResponse, CreateInteractionResponseMessage, EditInteractionResponse,
};

use crate::BotState;
use crate::cipherclerk::UserCipherclerk;
use crate::db::IdentityMode;
use crate::embeds;

/// Register the /cipherclerk command with all subcommands.
pub fn register() -> CreateCommand {
    CreateCommand::new("cipherclerk")
        .description("Manage your dregg cclerk")
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "create",
            "Create a new dregg cclerk",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "balance",
            "Check your cclerk balance",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "address",
            "Show your cell ID",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "export",
            "Show your private key (ephemeral)",
        ))
}

/// Handle /cipherclerk interactions.
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let subcommand = &command.data.options[0].name;

    match subcommand.as_str() {
        "create" => handle_create(ctx, command, state).await,
        "balance" => handle_balance(ctx, command, state).await,
        "address" => handle_address(ctx, command, state).await,
        "export" => handle_export(ctx, command, state).await,
        _ => {}
    }
}

async fn handle_create(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let discord_id = command.user.id.get().to_string();

    defer_ephemeral(ctx, command).await;

    // Check if user already has a cclerk.
    match state.db.user_exists(&discord_id).await {
        Ok(true) => {
            let embed = embeds::warning_embed(
                "Cipherclerk Exists",
                "You already have a dregg cclerk. Use `/cipherclerk address` to see your cell ID.",
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

    // Derive keys.
    let cclerk = UserCipherclerk::derive(
        &state.config.bot_secret,
        command.user.id.get(),
        state.federation_id_bytes,
    );
    let cell_id = cclerk.cell_id_hex().to_string();

    // Register on devnet.
    if let Err(e) = state
        .devnet
        .register_cell(&cell_id, cclerk.public_key_hex())
        .await
    {
        let embed = embeds::error_embed(
            "Devnet Error",
            &format!("Failed to register cell on devnet: {e}"),
        );
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    }

    // Store in database.
    if let Err(e) = state
        .db
        .register_user_with_mode(&discord_id, &cell_id, IdentityMode::Hosted, None)
        .await
    {
        let embed = embeds::error_embed("Database Error", &e.to_string());
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    }

    let embed = embeds::success_embed("Cipherclerk Created")
        .description("Your dregg cclerk is ready!")
        .field("Cell ID", format!("`{}`", cclerk.cell_id_short()), true)
        .field("Mode", "Hosted (custodial)", true);

    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
}

async fn handle_balance(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let discord_id = command.user.id.get().to_string();

    defer_ephemeral(ctx, command).await;

    let cell_id = match state.db.get_cell_id(&discord_id).await {
        Ok(Some(id)) => id,
        Ok(None) => {
            let embed = embeds::warning_embed(
                "No Cipherclerk",
                "You don't have a cclerk yet. Use `/cipherclerk create` first.",
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

    match state.devnet.get_balance(&cell_id).await {
        Ok(balance) => {
            let embed = embeds::dregg_embed("Cipherclerk Balance")
                .field("Balance", format!("{balance} DEC"), true)
                .field("Cell ID", format!("`{}...`", &cell_id[..16]), true);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed(
                "Devnet Offline",
                &format!(
                    "Could not query balance: {e}\n\nDevnet may be temporarily offline, try again later."
                ),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

async fn handle_address(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let discord_id = command.user.id.get().to_string();

    let cell_id = match state.db.get_cell_id(&discord_id).await {
        Ok(Some(id)) => id,
        Ok(None) => {
            let embed = embeds::warning_embed(
                "No Cipherclerk",
                "You don't have a cclerk yet. Use `/cipherclerk create` first.",
            );
            respond_ephemeral(ctx, command, embed).await;
            return;
        }
        Err(e) => {
            let embed = embeds::error_embed("Database Error", &e.to_string());
            respond_ephemeral(ctx, command, embed).await;
            return;
        }
    };

    let embed = embeds::dregg_embed("Your Cell Address")
        .field("Cell ID", format!("```\n{cell_id}\n```"), false)
        .field(
            "Explorer",
            format!("[View](https://devnet.dregg.fg-goose.online/explorer/cell/{cell_id})"),
            false,
        );

    respond_ephemeral(ctx, command, embed).await;
}

async fn handle_export(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let user_id = command.user.id.get();
    let discord_id = user_id.to_string();

    match state.db.user_exists(&discord_id).await {
        Ok(true) => {}
        Ok(false) => {
            let embed = embeds::warning_embed(
                "No Cipherclerk",
                "You don't have a cclerk yet. Use `/cipherclerk create` first.",
            );
            respond_ephemeral(ctx, command, embed).await;
            return;
        }
        Err(e) => {
            let embed = embeds::error_embed("Database Error", &e.to_string());
            respond_ephemeral(ctx, command, embed).await;
            return;
        }
    }

    let cclerk =
        UserCipherclerk::derive(&state.config.bot_secret, user_id, state.federation_id_bytes);

    let embed = embeds::dregg_embed("Private Key Export")
        .description("**Keep this secret!** Anyone with this key controls your cell.")
        .field(
            "Private Key",
            format!("```\n{}\n```", cclerk.private_key_hex()),
            false,
        )
        .field("Cell ID", format!("`{}`", cclerk.cell_id_short()), true);

    respond_ephemeral(ctx, command, embed).await;
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
