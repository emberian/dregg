//! pyana Discord Bot — custodial wallet and interactive devnet demo.
//!
//! Connects to the pyana devnet federation and provides slash commands for
//! wallet management, token transfers, an explorer for browsing devnet state,
//! a presence attestation system for proof-of-presence capability tokens,
//! CapTP integration (the bot as a capability peer), programmable queues,
//! governance, name service, and bidirectional pyana<->Discord integration.

mod activity_feed;
pub mod captp_client;
mod commands;
mod config;
mod db;
mod devnet;
pub mod discord_caps;
mod embeds;
pub mod presence;
mod wallet;

use std::sync::Arc;

use serenity::Client;
use serenity::all::{
    Command, Context, EventHandler, GatewayIntents, Interaction, Message, Presence, Ready,
};
use serenity::async_trait;
use tokio::sync::Mutex;
use tracing::{error, info};

use captp_client::CapTPClient;
use config::Config;
use db::Database;
use devnet::DevnetClient;
use discord_caps::{DiscordCapRegistry, EventBridge};
use presence::{PresenceStatus, PresenceTracker};

/// Shared bot state accessible from all command handlers.
pub struct BotState {
    pub config: Config,
    pub db: Database,
    pub devnet: DevnetClient,
    pub presence: Mutex<PresenceTracker>,
    /// The bot's CapTP client — its identity and capability management.
    pub captp: CapTPClient,
    /// Registry of Discord capabilities exercisable via CapTP.
    pub discord_caps: DiscordCapRegistry,
    /// Event bridge: Discord events → pyana turns.
    pub event_bridge: EventBridge,
    /// The federation id this bot binds wallet signatures to. Threaded
    /// through every per-user `UserWallet::derive(...)` call so the
    /// AppWallet's action signatures are bound to the correct group.
    pub federation_id_bytes: [u8; 32],
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
        //
        // Commands tied to apps deleted from the workspace (AMM `swap`/
        // `pool`/`lend`, orderbook `order`/`book`/`trades`) were retired
        // in the post-relocation cleanup; their slash-command names will
        // disappear from Discord once this set is re-registered.
        let commands = vec![
            // ─── Bot core ───────────────────────────────────────────────────
            commands::explorer::register(),
            commands::presence::register(),
            commands::wallet::register(),
            commands::transfer::register_send(),
            commands::transfer::register_tip(),
            commands::gallery::register(),
            commands::identity::register(),
            commands::status::register_status(),
            commands::status::register_proof(),
            commands::status::register_metrics(),
            commands::social::register_faucet(),
            commands::social::register_leaderboard(),
            commands::social::register_history(),
            // ─── CapTP commands ─────────────────────────────────────────────
            commands::captp::register_share(),
            commands::captp::register_accept(),
            commands::captp::register_delegate(),
            commands::captp::register_list(),
            commands::captp::register_revoke(),
            // ─── Programmable queue commands ─────────────────────────────────
            commands::queue::register_create(),
            commands::queue::register_publish(),
            commands::queue::register_subscribe(),
            commands::queue::register_status(),
            commands::queue::register_mount(),
            // ─── Governance commands ────────────────────────────────────────
            commands::governance::register_propose(),
            commands::governance::register_vote(),
            commands::governance::register_status(),
            commands::governance::register_routes(),
            // ─── Name service commands ──────────────────────────────────────
            commands::names::register_register(),
            commands::names::register_resolve(),
            commands::names::register_whois(),
            // ─── Federation setup commands ──────────────────────────────────
            commands::federation::register_setup(),
            commands::federation::register_link(),
            commands::federation::register_unlink(),
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
                // ─── Bot core ───────────────────────────────────────────────
                "explorer" => commands::explorer::handle(&ctx, &command, &self.state).await,
                "presence" => commands::presence::handle(&ctx, &command, &self.state).await,
                "wallet" => commands::wallet::handle(&ctx, &command, &self.state).await,
                "send" | "tip" => commands::transfer::handle(&ctx, &command, &self.state).await,
                "gallery" => commands::gallery::handle(&ctx, &command, &self.state).await,
                "credential" => commands::identity::handle(&ctx, &command, &self.state).await,
                "status" => commands::status::handle_status(&ctx, &command, &self.state).await,
                "proof" => commands::status::handle_proof(&ctx, &command, &self.state).await,
                "metrics" => commands::status::handle_metrics(&ctx, &command, &self.state).await,
                "faucet" => commands::social::handle_faucet(&ctx, &command, &self.state).await,
                "leaderboard" => {
                    commands::social::handle_leaderboard(&ctx, &command, &self.state).await
                }
                "history" => commands::social::handle_history(&ctx, &command, &self.state).await,
                // ─── CapTP commands ─────────────────────────────────────────
                "cap-share" => commands::captp::handle_share(&ctx, &command, &self.state).await,
                "cap-accept" => commands::captp::handle_accept(&ctx, &command, &self.state).await,
                "cap-delegate" => {
                    commands::captp::handle_delegate(&ctx, &command, &self.state).await
                }
                "cap-list" => commands::captp::handle_list(&ctx, &command, &self.state).await,
                "cap-revoke" => commands::captp::handle_revoke(&ctx, &command, &self.state).await,
                // ─── Programmable queue commands ─────────────────────────────
                "queue-create" => commands::queue::handle_create(&ctx, &command, &self.state).await,
                "queue-publish" => {
                    commands::queue::handle_publish(&ctx, &command, &self.state).await
                }
                "queue-subscribe" => {
                    commands::queue::handle_subscribe(&ctx, &command, &self.state).await
                }
                "queue-status" => commands::queue::handle_status(&ctx, &command, &self.state).await,
                "queue-mount" => commands::queue::handle_mount(&ctx, &command, &self.state).await,
                // ─── Governance commands ────────────────────────────────────
                "gov-propose" => {
                    commands::governance::handle_propose(&ctx, &command, &self.state).await
                }
                "gov-vote" => commands::governance::handle_vote(&ctx, &command, &self.state).await,
                "gov-status" => {
                    commands::governance::handle_status(&ctx, &command, &self.state).await
                }
                "gov-routes" => {
                    commands::governance::handle_routes(&ctx, &command, &self.state).await
                }
                // ─── Name service commands ──────────────────────────────────
                "name-register" => {
                    commands::names::handle_register(&ctx, &command, &self.state).await
                }
                "name-resolve" => {
                    commands::names::handle_resolve(&ctx, &command, &self.state).await
                }
                "name-whois" => commands::names::handle_whois(&ctx, &command, &self.state).await,
                // ─── Federation setup commands ──────────────────────────────
                "setup-federation" => {
                    commands::federation::handle_setup(&ctx, &command, &self.state).await
                }
                "link-wallet" => {
                    commands::federation::handle_link(&ctx, &command, &self.state).await
                }
                "unlink-wallet" => {
                    commands::federation::handle_unlink(&ctx, &command, &self.state).await
                }
                _ => {
                    tracing::warn!("Unknown command: {name}");
                }
            }
        }
    }

    async fn message(&self, _ctx: Context, msg: Message) {
        // Bridge messages to pyana queues if the channel is linked.
        self.state.event_bridge.on_message(&msg).await;
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

    // Build CapTP client (the bot's own pyana identity).
    //
    // The bot's own wallet is the user_id == 0 derivation. We use the
    // canonical AppWallet so the bot's identity (cell id, public key)
    // is computed the same way as any other pyana agent.
    let federation_id_bytes = [0u8; 32]; // Will be configured per-deployment.
    let bot_cell_id = {
        let wallet = wallet::UserWallet::derive(&config.bot_secret, 0, federation_id_bytes);
        wallet.cell_id_hex().to_string()
    };
    let federation_id = pyana_captp::FederationId(federation_id_bytes);
    let captp = CapTPClient::new(
        federation_id,
        bot_cell_id.clone(),
        config.devnet_url.clone(),
    );
    info!(
        "CapTP client initialized, bot cell: {}...",
        &bot_cell_id[..16]
    );

    // Build Discord capability registry and event bridge.
    let discord_caps = DiscordCapRegistry::new();
    let event_bridge = EventBridge::new(config.devnet_url.clone());

    // Build shared state.
    let state = Arc::new(BotState {
        config,
        db,
        devnet,
        presence,
        captp,
        discord_caps,
        event_bridge,
        federation_id_bytes,
    });

    // Build Discord client (GUILD_PRESENCES + GUILD_MESSAGES for message bridging).
    let intents = GatewayIntents::GUILD_PRESENCES
        | GatewayIntents::GUILD_MESSAGES
        | GatewayIntents::MESSAGE_CONTENT
        | GatewayIntents::GUILD_MESSAGE_REACTIONS;
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
