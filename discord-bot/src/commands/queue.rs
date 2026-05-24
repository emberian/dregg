//! Programmable queue commands: `/queue-create`, `/queue-publish`, `/queue-subscribe`,
//! `/queue-status`, `/queue-mount`.
//!
//! Discord channels become programmable queues mounted in the pyana namespace at
//! `/discord/<guild-id>/<name>`.

use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, CreateInteractionResponse, CreateInteractionResponseMessage,
    EditInteractionResponse,
};

use crate::BotState;
use crate::embeds;

// ─── Registration ───────────────────────────────────────────────────────────

/// Register `/queue-create <name> [--acl role] [--rate-limit N] [--deposit min]`.
pub fn register_create() -> CreateCommand {
    CreateCommand::new("queue-create")
        .description("Create a programmable queue mounted in the guild namespace")
        .add_option(
            CreateCommandOption::new(CommandOptionType::String, "name", "Queue name")
                .required(true),
        )
        .add_option(CreateCommandOption::new(
            CommandOptionType::Role,
            "acl",
            "Required role to publish (optional)",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::Integer,
            "rate-limit",
            "Max messages per minute (optional)",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::Integer,
            "deposit",
            "Minimum deposit per message in computrons (optional)",
        ))
}

/// Register `/queue-publish <name> <message>`.
pub fn register_publish() -> CreateCommand {
    CreateCommand::new("queue-publish")
        .description("Publish a message to a programmable queue")
        .add_option(
            CreateCommandOption::new(CommandOptionType::String, "name", "Queue name")
                .required(true),
        )
        .add_option(
            CreateCommandOption::new(CommandOptionType::String, "message", "Message to publish")
                .required(true),
        )
}

/// Register `/queue-subscribe <name>`.
pub fn register_subscribe() -> CreateCommand {
    CreateCommand::new("queue-subscribe")
        .description("Subscribe to a queue (receive DMs on new messages)")
        .add_option(
            CreateCommandOption::new(CommandOptionType::String, "name", "Queue name")
                .required(true),
        )
}

/// Register `/queue-status <name>`.
pub fn register_status() -> CreateCommand {
    CreateCommand::new("queue-status")
        .description("Show queue stats: depth, subscribers, deposits")
        .add_option(
            CreateCommandOption::new(CommandOptionType::String, "name", "Queue name")
                .required(true),
        )
}

/// Register `/queue-mount <name> <pyana-uri>`.
pub fn register_mount() -> CreateCommand {
    CreateCommand::new("queue-mount")
        .description("Mount an external pyana queue in this guild")
        .add_option(
            CreateCommandOption::new(CommandOptionType::String, "name", "Local mount name")
                .required(true),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::String,
                "uri",
                "pyana:// URI of the external queue",
            )
            .required(true),
        )
}

// ─── Handlers ───────────────────────────────────────────────────────────────

/// Handle `/queue-create`.
pub async fn handle_create(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let name = get_string_option(&command.data.options, "name").unwrap_or_default();
    let acl_role = command
        .data
        .options
        .iter()
        .find(|o| o.name == "acl")
        .and_then(|o| match &o.value {
            CommandDataOptionValue::Role(r) => Some(r.get()),
            _ => None,
        });
    let rate_limit = get_integer_option(&command.data.options, "rate-limit");
    let deposit = get_integer_option(&command.data.options, "deposit");

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

    defer_ephemeral(ctx, command).await;

    let namespace_path = format!("/discord/{guild_id}/{name}");

    let url = format!("{}/queues/create", state.config.devnet_url);
    let mut body = serde_json::json!({
        "name": name,
        "namespace_path": namespace_path,
        "guild_id": guild_id,
        "creator": state.captp.bot_cell_id,
    });

    if let Some(role) = acl_role {
        body["acl_role"] = serde_json::json!(role);
    }
    if let Some(rl) = rate_limit {
        body["rate_limit"] = serde_json::json!(rl);
    }
    if let Some(dep) = deposit {
        body["min_deposit"] = serde_json::json!(dep);
    }

    let resp = state.devnet.client().post(&url).json(&body).send().await;

    match resp {
        Ok(r) if r.status().is_success() => {
            let embed = embeds::success_embed("Queue Created")
                .field("Name", &name, true)
                .field("Path", format!("`{namespace_path}`"), true)
                .field(
                    "Rate Limit",
                    rate_limit.map_or("none".to_string(), |r| format!("{r}/min")),
                    true,
                )
                .field(
                    "Min Deposit",
                    deposit.map_or("none".to_string(), |d| format!("{d} computrons")),
                    true,
                );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Ok(r) => {
            let body = r.text().await.unwrap_or_default();
            let embed = embeds::error_embed("Queue Creation Failed", &body);
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

/// Handle `/queue-publish`.
pub async fn handle_publish(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let name = get_string_option(&command.data.options, "name").unwrap_or_default();
    let message = get_string_option(&command.data.options, "message").unwrap_or_default();

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

    defer_ephemeral(ctx, command).await;

    let namespace_path = format!("/discord/{guild_id}/{name}");
    let url = format!("{}/queues/publish", state.config.devnet_url);
    let body = serde_json::json!({
        "namespace_path": namespace_path,
        "message": message,
        "publisher": state.captp.bot_cell_id,
        "sender_discord_id": command.user.id.get(),
    });

    let resp = state.devnet.client().post(&url).json(&body).send().await;

    match resp {
        Ok(r) if r.status().is_success() => {
            let embed = embeds::success_embed("Published")
                .field("Queue", &name, true)
                .field("Message", format!("`{}`", truncate(&message, 100)), false);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Ok(r) => {
            let body = r.text().await.unwrap_or_default();
            let embed = embeds::error_embed("Publish Failed", &body);
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

/// Handle `/queue-subscribe`.
pub async fn handle_subscribe(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let name = get_string_option(&command.data.options, "name").unwrap_or_default();

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

    defer_ephemeral(ctx, command).await;

    let namespace_path = format!("/discord/{guild_id}/{name}");
    let discord_id = command.user.id.get().to_string();
    let url = format!("{}/queues/subscribe", state.config.devnet_url);
    let body = serde_json::json!({
        "namespace_path": namespace_path,
        "subscriber_discord_id": discord_id,
        "subscriber_cell": state.captp.bot_cell_id,
    });

    let resp = state.devnet.client().post(&url).json(&body).send().await;

    match resp {
        Ok(r) if r.status().is_success() => {
            let embed = embeds::success_embed("Subscribed")
                .description(format!(
                    "You will receive DMs when new messages arrive in **{name}**."
                ))
                .field("Queue", &name, true)
                .field("Path", format!("`{namespace_path}`"), true);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Ok(r) => {
            let body = r.text().await.unwrap_or_default();
            let embed = embeds::error_embed("Subscribe Failed", &body);
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

/// Handle `/queue-status`.
pub async fn handle_status(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let name = get_string_option(&command.data.options, "name").unwrap_or_default();

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

    defer_ephemeral(ctx, command).await;

    let namespace_path = format!("/discord/{guild_id}/{name}");
    let url = format!(
        "{}/queues/status?path={}",
        state.config.devnet_url, namespace_path
    );

    let resp = state.devnet.client().get(&url).send().await;

    match resp {
        Ok(r) if r.status().is_success() => {
            let status: QueueStatusResponse = match r.json().await {
                Ok(s) => s,
                Err(e) => {
                    let embed = embeds::error_embed("Parse Error", &e.to_string());
                    let _ = command
                        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                        .await;
                    return;
                }
            };

            let embed = embeds::pyana_embed("Queue Status")
                .field("Name", &name, true)
                .field("Depth", status.depth.to_string(), true)
                .field("Subscribers", status.subscribers.to_string(), true)
                .field(
                    "Total Deposits",
                    format!("{} computrons", status.total_deposits),
                    true,
                )
                .field("Path", format!("`{namespace_path}`"), false);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Ok(r) => {
            let body = r.text().await.unwrap_or_default();
            let embed = embeds::error_embed("Status Unavailable", &body);
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

/// Handle `/queue-mount`.
pub async fn handle_mount(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let name = get_string_option(&command.data.options, "name").unwrap_or_default();
    let uri = get_string_option(&command.data.options, "uri").unwrap_or_default();

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

    defer_ephemeral(ctx, command).await;

    let namespace_path = format!("/discord/{guild_id}/{name}");
    let url = format!("{}/queues/mount", state.config.devnet_url);
    let body = serde_json::json!({
        "namespace_path": namespace_path,
        "external_uri": uri,
        "mounter": state.captp.bot_cell_id,
        "guild_id": guild_id,
    });

    let resp = state.devnet.client().post(&url).json(&body).send().await;

    match resp {
        Ok(r) if r.status().is_success() => {
            let embed = embeds::success_embed("Queue Mounted")
                .description("External pyana queue is now accessible in this guild.")
                .field("Local Name", &name, true)
                .field("Path", format!("`{namespace_path}`"), true)
                .field("External URI", format!("`{}`", truncate(&uri, 60)), false);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Ok(r) => {
            let body = r.text().await.unwrap_or_default();
            let embed = embeds::error_embed("Mount Failed", &body);
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
struct QueueStatusResponse {
    depth: u64,
    subscribers: u64,
    total_deposits: u64,
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

fn get_integer_option(options: &[serenity::all::CommandDataOption], name: &str) -> Option<i64> {
    options
        .iter()
        .find(|o| o.name == name)
        .and_then(|o| match &o.value {
            CommandDataOptionValue::Integer(n) => Some(*n),
            _ => None,
        })
}

fn truncate(s: &str, max: usize) -> String {
    if s.len() > max {
        format!("{}...", &s[..max])
    } else {
        s.to_string()
    }
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
