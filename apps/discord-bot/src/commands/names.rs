//! Name service commands: `/name-register`, `/name-resolve`, `/name-whois`.
//!
//! Guild-scoped namespace registration and resolution via the pyana governed namespace.

use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, CreateInteractionResponse, CreateInteractionResponseMessage,
    EditInteractionResponse,
};

use crate::BotState;
use crate::embeds;

// ─── Registration ───────────────────────────────────────────────────────────

/// Register `/name-register <name>`.
pub fn register_register() -> CreateCommand {
    CreateCommand::new("name-register")
        .description("Register a name in the guild's namespace")
        .add_option(
            CreateCommandOption::new(CommandOptionType::String, "name", "Name to register")
                .required(true),
        )
}

/// Register `/name-resolve <name>`.
pub fn register_resolve() -> CreateCommand {
    CreateCommand::new("name-resolve")
        .description("Resolve a name to a sturdy ref")
        .add_option(
            CreateCommandOption::new(CommandOptionType::String, "name", "Name to resolve")
                .required(true),
        )
}

/// Register `/name-whois <cell-id>`.
pub fn register_whois() -> CreateCommand {
    CreateCommand::new("name-whois")
        .description("Reverse lookup: find the name registered to a cell ID")
        .add_option(
            CreateCommandOption::new(CommandOptionType::String, "cell-id", "Cell ID to look up")
                .required(true),
        )
}

// ─── Handlers ───────────────────────────────────────────────────────────────

/// Handle `/name-register`.
pub async fn handle_register(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let name = get_string_option(&command.data.options, "name").unwrap_or_default();

    let guild_id = match command.guild_id {
        Some(id) => id.get(),
        None => {
            respond_error(
                ctx,
                command,
                "Guild Required",
                "Name service commands must be run in a server.",
            )
            .await;
            return;
        }
    };

    defer_ephemeral(ctx, command).await;

    let discord_id = command.user.id.get().to_string();
    let cell_id = match state.db.get_cell_id(&discord_id).await {
        Ok(Some(id)) => id,
        Ok(None) => {
            let embed = embeds::warning_embed(
                "No Wallet",
                "You need a linked pyana identity to register names. Use `/link-wallet` first.",
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

    let url = format!("{}/names/register", state.config.devnet_url);
    let body = serde_json::json!({
        "guild_id": guild_id,
        "name": name,
        "owner": cell_id,
    });

    let resp = state.devnet.client().post(&url).json(&body).send().await;

    match resp {
        Ok(r) if r.status().is_success() => {
            let result: NameRegisterResponse = match r.json().await {
                Ok(n) => n,
                Err(e) => {
                    let embed = embeds::error_embed("Parse Error", &e.to_string());
                    let _ = command
                        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                        .await;
                    return;
                }
            };

            let embed = embeds::success_embed("Name Registered")
                .field("Name", &name, true)
                .field("Path", format!("`{}`", result.full_path), true)
                .field(
                    "Owner",
                    format!("`{}...`", &cell_id[..16.min(cell_id.len())]),
                    true,
                );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Ok(r) => {
            let body = r.text().await.unwrap_or_default();
            let embed = embeds::error_embed("Registration Failed", &body);
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

/// Handle `/name-resolve`.
pub async fn handle_resolve(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let name = get_string_option(&command.data.options, "name").unwrap_or_default();

    let guild_id = match command.guild_id {
        Some(id) => id.get(),
        None => {
            respond_error(
                ctx,
                command,
                "Guild Required",
                "Name service commands must be run in a server.",
            )
            .await;
            return;
        }
    };

    defer_ephemeral(ctx, command).await;

    let url = format!(
        "{}/names/resolve?guild_id={guild_id}&name={name}",
        state.config.devnet_url
    );

    let resp = state.devnet.client().get(&url).send().await;

    match resp {
        Ok(r) if r.status().is_success() => {
            let result: NameResolveResponse = match r.json().await {
                Ok(n) => n,
                Err(e) => {
                    let embed = embeds::error_embed("Parse Error", &e.to_string());
                    let _ = command
                        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                        .await;
                    return;
                }
            };

            let embed = embeds::pyana_embed("Name Resolved")
                .field("Name", &name, true)
                .field("Cell ID", format!("`{}`", result.cell_id), false)
                .field("URI", format!("```\n{}\n```", result.uri), false)
                .field(
                    "Owner",
                    format!("`{}...`", &result.owner[..16.min(result.owner.len())]),
                    true,
                );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Ok(r) if r.status().as_u16() == 404 => {
            let embed = embeds::warning_embed(
                "Name Not Found",
                &format!("No registration found for `{name}` in this guild."),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Ok(r) => {
            let body = r.text().await.unwrap_or_default();
            let embed = embeds::error_embed("Resolve Failed", &body);
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

/// Handle `/name-whois`.
pub async fn handle_whois(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let cell_id = get_string_option(&command.data.options, "cell-id").unwrap_or_default();

    let guild_id = match command.guild_id {
        Some(id) => id.get(),
        None => {
            respond_error(
                ctx,
                command,
                "Guild Required",
                "Name service commands must be run in a server.",
            )
            .await;
            return;
        }
    };

    defer_ephemeral(ctx, command).await;

    let url = format!(
        "{}/names/whois?guild_id={guild_id}&cell_id={cell_id}",
        state.config.devnet_url
    );

    let resp = state.devnet.client().get(&url).send().await;

    match resp {
        Ok(r) if r.status().is_success() => {
            let result: WhoisResponse = match r.json().await {
                Ok(w) => w,
                Err(e) => {
                    let embed = embeds::error_embed("Parse Error", &e.to_string());
                    let _ = command
                        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                        .await;
                    return;
                }
            };

            let mut desc = format!("**Cell:** `{}`\n", cell_id);
            if !result.names.is_empty() {
                desc.push_str("\n**Registered Names:**\n");
                for name in &result.names {
                    desc.push_str(&format!("- `{name}`\n"));
                }
            } else {
                desc.push_str("\nNo names registered for this cell in this guild.");
            }

            let embed = embeds::pyana_embed("Whois").description(desc);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Ok(r) => {
            let body = r.text().await.unwrap_or_default();
            let embed = embeds::error_embed("Whois Failed", &body);
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

// ─── Wire types ─────────────────────────────────────────────────────────────

#[derive(serde::Deserialize)]
struct NameRegisterResponse {
    full_path: String,
}

#[derive(serde::Deserialize)]
struct NameResolveResponse {
    cell_id: String,
    uri: String,
    owner: String,
}

#[derive(serde::Deserialize)]
struct WhoisResponse {
    names: Vec<String>,
}

// ─── Helpers ────────────────────────────────────────────────────────────────

fn get_string_option(options: &[serenity::all::CommandDataOption], name: &str) -> Option<String> {
    options
        .iter()
        .find(|o| o.name == name)
        .and_then(|o| match &o.value {
            CommandDataOptionValue::String(s) => Some(s.clone()),
            _ => None,
        })
}

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
