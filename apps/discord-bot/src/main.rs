//! pyana Discord Bot — custodial wallet and interactive devnet demo.
//!
//! Connects to the pyana devnet federation and provides slash commands for
//! wallet management, token transfers, an explorer for browsing devnet state,
//! and a presence attestation system for proof-of-presence capability tokens.

mod activity_feed;
mod commands;
mod config;
mod db;
mod devnet;
mod embeds;
pub mod presence;
mod wallet;

use std::sync::Arc;

use serenity::Client;
use serenity::all::{
    Command, Context, EventHandler, GatewayIntents, Interaction, Presence, Ready,
};
use serenity::async_trait;
use tokio::sync::Mutex;
use tracing::{error, info};

use config::Config;
use db::Database;
use devnet::DevnetClient;
use presence::{PresenceStatus, PresenceTracker};

/// Shared bot state accessible from all command handlers.
pub struct BotState {
    pub config: Config,
    pub db: Database,
    pub devnet: DevnetClient,
    pub presence: Mutex<PresenceTracker>,
}

/// The main event handler for Discord gateway events.
struct Handler {
    state: Arc<BotState>,
}

#[async_trait]
impl EventHandler for Handler {
    async fn ready(&self, ctx: Context, ready: Ready) {
        info!("Bot connected as {}", ready.user.name);

        // Register global slash commands.
        let commands = vec![
            commands::explorer::register(),
            commands::presence::register(),
        ];

        match Command::set_global_commands(&ctx.http, commands).await {
            Ok(cmds) => info!("Registered {} global slash commands", cmds.len()),
            Err(e) => error!("Failed to register commands: {e}"),
        }

        // Start the activity feed background task.
        activity_feed::start(self.state.clone(), ctx.http.clone());
    }

    async fn interaction_create(&self, ctx: Context, interaction: Interaction) {
        if let Interaction::Command(command) = interaction {
            let name = command.data.name.as_str();

            match name {
                "explorer" => commands::explorer::handle(&ctx, &command, &self.state).await,
                "presence" => commands::presence::handle(&ctx, &command, &self.state).await,
                _ => {
                    tracing::warn!("Unknown command: {name}");
                }
            }
        }
    }

    async fn presence_update(&self, _ctx: Context, data: Presence) {
        let user_id = data.user.id.get();

        // Map serenity's OnlineStatus to our PresenceStatus.
        let status = match data.status {
            serenity::all::OnlineStatus::Online => PresenceStatus::Online,
            serenity::all::OnlineStatus::Idle => PresenceStatus::Idle,
            serenity::all::OnlineStatus::DoNotDisturb => PresenceStatus::Dnd,
            serenity::all::OnlineStatus::Offline | serenity::all::OnlineStatus::Invisible => {
                PresenceStatus::Offline
            }
            _ => PresenceStatus::Offline,
        };

        let mut tracker = self.state.presence.lock().await;
        let (old, new) = tracker.update(user_id, status);

        // Log significant transitions.
        if let Some(old_status) = old {
            if old_status != new {
                tracing::debug!(
                    user_id,
                    old = %old_status,
                    new = %new,
                    "Presence update"
                );
            }
        }
    }
}

#[tokio::main]
async fn main() {
    // Initialize tracing.
    tracing_subscriber::fmt()
        .with_env_filter(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| tracing_subscriber::EnvFilter::new("info")),
        )
        .init();

    info!("Starting pyana Discord bot...");

    // Load configuration.
    let config = Config::from_env();

    // Connect to database.
    let db = Database::connect(&config.database_url)
        .await
        .expect("failed to connect to database");
    info!("Database connected");

    // Create devnet client.
    let devnet = DevnetClient::new(&config.devnet_url);
    info!("Devnet client configured for {}", config.devnet_url);

    // Build presence tracker.
    let presence = Mutex::new(PresenceTracker::new(config.bot_secret));
    info!("Presence tracker initialized");

    // Build shared state.
    let state = Arc::new(BotState { config, db, devnet, presence });

    // Build Discord client (GUILD_PRESENCES required for presence tracking).
    let intents = GatewayIntents::GUILD_PRESENCES;
    let mut client = Client::builder(&state.config.discord_token, intents)
        .event_handler(Handler {
            state: state.clone(),
        })
        .await
        .expect("failed to create Discord client");

    // Start the bot.
    info!("Connecting to Discord...");
    if let Err(e) = client.start().await {
        error!("Bot error: {e}");
    }
}
