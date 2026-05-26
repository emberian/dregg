//! Programmable queue commands: `/queue-create`, `/queue-publish`, `/queue-subscribe`,
//! `/queue-status`, `/queue-mount`.
//!
//! Discord channels become programmable queues mounted in the dregg namespace at
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

/// Register `/queue-mount <name> <dregg-uri>`.
pub fn register_mount() -> CreateCommand {
    CreateCommand::new("queue-mount")
        .description("Mount an external dregg queue in this guild")
        .add_option(
            CreateCommandOption::new(CommandOptionType::String, "name", "Local mount name")
                .required(true),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::String,
                "uri",
                "dregg:// URI of the external queue",
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

    let url = format!("{}/queues/allocate", state.config.devnet_url);
    let capacity = rate_limit.unwrap_or(1024).max(1) as u64;
    let body = serde_json::json!({
        "capacity": capacity,
        "program_vk": serde_json::Value::Null,
    });

    let resp = state.devnet.client().post(&url).json(&body).send().await;

    match resp {
        Ok(r) if r.status().is_success() => {
            let allocated: QueueAllocateResponse = match r.json().await {
                Ok(value) => value,
                Err(e) => {
                    let embed = embeds::error_embed("Parse Error", &e.to_string());
                    let _ = command
                        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                        .await;
                    return;
                }
            };
            let acl_role_str = acl_role.map(|role| role.to_string());
            let actor = command.user.id.get().to_string();
            if let Err(e) = state
                .db
                .upsert_starbridge_queue(
                    &namespace_path,
                    &guild_id.to_string(),
                    &name,
                    &allocated.queue_id,
                    &actor,
                    acl_role_str.as_deref(),
                    rate_limit,
                    deposit,
                )
                .await
            {
                let embed = embeds::error_embed("Queue State Error", &e.to_string());
                let _ = command
                    .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                    .await;
                return;
            }
            let _ = state
                .db
                .record_starbridge_activity(
                    "subscription",
                    "queue.allocate",
                    &actor,
                    Some(&guild_id.to_string()),
                    Some(&namespace_path),
                    "accepted",
                    serde_json::json!({
                        "queue_id": allocated.queue_id,
                        "capacity": capacity,
                    }),
                )
                .await;
            let embed = embeds::success_embed("Queue Created")
                .field("Name", &name, true)
                .field("Path", format!("`{namespace_path}`"), true)
                .field("Queue ID", short_queue(&allocated.queue_id), true)
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
    let queue = match state.db.get_starbridge_queue(&namespace_path).await {
        Ok(Some(queue)) => queue,
        Ok(None) => {
            let embed = embeds::warning_embed(
                "Queue Not Found",
                &format!("No queue is mounted at `{namespace_path}`. Run `/queue-create` first."),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
        Err(e) => {
            let embed = embeds::error_embed("Queue State Error", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
    };
    let url = format!(
        "{}/queues/{}/enqueue",
        state.config.devnet_url, queue.queue_id
    );
    let body = serde_json::json!({
        "message_hash": message_hash_hex(&message),
        "deposit": 0,
    });

    let resp = state.devnet.client().post(&url).json(&body).send().await;

    match resp {
        Ok(r) if r.status().is_success() => {
            let result: QueueEnqueueResponse = r
                .json()
                .await
                .unwrap_or(QueueEnqueueResponse { position: 0 });
            let actor = command.user.id.get().to_string();
            let _ = state
                .db
                .record_starbridge_activity(
                    "subscription",
                    "queue.enqueue",
                    &actor,
                    Some(&guild_id.to_string()),
                    Some(&namespace_path),
                    "accepted",
                    serde_json::json!({
                        "queue_id": queue.queue_id,
                        "position": result.position,
                        "message_hash": message_hash_hex(&message),
                    }),
                )
                .await;
            let embed = embeds::success_embed("Published")
                .field("Queue", &name, true)
                .field("Position", result.position.to_string(), true)
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
    match state.db.get_starbridge_queue(&namespace_path).await {
        Ok(Some(_)) => {}
        Ok(None) => {
            let embed = embeds::warning_embed(
                "Queue Not Found",
                &format!("No queue is mounted at `{namespace_path}`. Run `/queue-create` first."),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
        Err(e) => {
            let embed = embeds::error_embed("Queue State Error", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
    }

    let discord_id = command.user.id.get().to_string();
    match state
        .db
        .subscribe_starbridge_queue(&namespace_path, &discord_id)
        .await
    {
        Ok(inserted) => {
            let _ = state
                .db
                .record_starbridge_activity(
                    "subscription",
                    "queue.subscribe",
                    &discord_id,
                    Some(&guild_id.to_string()),
                    Some(&namespace_path),
                    if inserted { "accepted" } else { "unchanged" },
                    serde_json::json!({}),
                )
                .await;
            let embed = embeds::success_embed(if inserted {
                "Subscribed"
            } else {
                "Already Subscribed"
            })
            .description(format!(
                "You will receive DMs when new messages arrive in **{name}**."
            ))
            .field("Queue", &name, true)
            .field("Path", format!("`{namespace_path}`"), true);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Subscribe Failed", &e.to_string());
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
    let queue = match state.db.get_starbridge_queue(&namespace_path).await {
        Ok(Some(queue)) => queue,
        Ok(None) => {
            let embed = embeds::warning_embed(
                "Queue Not Found",
                &format!("No queue is mounted at `{namespace_path}`."),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
        Err(e) => {
            let embed = embeds::error_embed("Queue State Error", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
    };
    let url = format!(
        "{}/queues/{}/status",
        state.config.devnet_url, queue.queue_id
    );

    let resp = state.devnet.client().get(&url).send().await;

    match resp {
        Ok(r) if r.status().is_success() => {
            let status: QueueNodeStatusResponse = match r.json().await {
                Ok(s) => s,
                Err(e) => {
                    let embed = embeds::error_embed("Parse Error", &e.to_string());
                    let _ = command
                        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                        .await;
                    return;
                }
            };
            let subscribers = state
                .db
                .count_starbridge_queue_subscribers(&namespace_path)
                .await
                .unwrap_or(0);

            let embed = embeds::dregg_embed("Queue Status")
                .field("Name", &name, true)
                .field("Occupancy", status.occupancy.to_string(), true)
                .field("Capacity", status.capacity.to_string(), true)
                .field("Subscribers", subscribers.to_string(), true)
                .field(
                    "Rate Limit",
                    queue
                        .rate_limit
                        .map_or("none".to_string(), |r| format!("{r}/min")),
                    true,
                )
                .field("Queue ID", short_queue(&status.queue_id), true)
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
    let Some(queue_id) = queue_id_from_uri(&uri) else {
        let embed = embeds::error_embed(
            "Invalid Queue URI",
            "Mount expects a URI ending in a 64-character hex queue id.",
        );
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    };
    let actor = command.user.id.get().to_string();

    match state
        .db
        .upsert_starbridge_queue(
            &namespace_path,
            &guild_id.to_string(),
            &name,
            &queue_id,
            &actor,
            None,
            None,
            None,
        )
        .await
    {
        Ok(()) => {
            let _ = state
                .db
                .record_starbridge_activity(
                    "subscription",
                    "queue.mount",
                    &actor,
                    Some(&guild_id.to_string()),
                    Some(&namespace_path),
                    "accepted",
                    serde_json::json!({
                        "queue_id": queue_id,
                        "uri": uri,
                    }),
                )
                .await;
            let embed = embeds::success_embed("Queue Mounted")
                .description("External dregg queue is now accessible in this guild.")
                .field("Local Name", &name, true)
                .field("Path", format!("`{namespace_path}`"), true)
                .field("Queue ID", short_queue(&queue_id), true)
                .field("External URI", format!("`{}`", truncate(&uri, 60)), false);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Mount Failed", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

// ─── Wire types ─────────────────────────────────────────────────────────────

#[derive(serde::Deserialize)]
struct QueueAllocateResponse {
    #[serde(rename = "queueId")]
    queue_id: String,
}

#[derive(serde::Deserialize)]
struct QueueEnqueueResponse {
    position: u64,
}

#[derive(serde::Deserialize)]
struct QueueNodeStatusResponse {
    #[serde(rename = "queueId")]
    queue_id: String,
    occupancy: u64,
    capacity: u64,
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

fn message_hash_hex(message: &str) -> String {
    hex::encode(blake3::hash(message.as_bytes()).as_bytes())
}

fn short_queue(queue_id: &str) -> String {
    format!("`{}...`", &queue_id[..16.min(queue_id.len())])
}

fn queue_id_from_uri(uri: &str) -> Option<String> {
    let candidate = uri
        .trim_end_matches('/')
        .rsplit(['/', ':'])
        .next()
        .unwrap_or_default();
    if candidate.len() == 64 && candidate.chars().all(|ch| ch.is_ascii_hexdigit()) {
        Some(candidate.to_ascii_lowercase())
    } else {
        None
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
