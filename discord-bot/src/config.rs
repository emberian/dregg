//! Environment-based configuration for the Discord bot.

use std::env;

/// Bot configuration loaded from environment variables.
#[derive(Clone)]
pub struct Config {
    /// Discord bot token.
    pub discord_token: String,
    /// Discord application ID (for slash command registration).
    pub discord_app_id: u64,
    /// Secret used for deterministic key derivation (32 bytes hex-encoded).
    pub bot_secret: [u8; 32],
    /// Base URL for the devnet API.
    pub devnet_url: String,
    /// SQLite database URL.
    pub database_url: String,
}

impl Config {
    /// Load configuration from environment variables.
    ///
    /// # Panics
    ///
    /// Panics if required environment variables are missing or malformed.
    pub fn from_env() -> Self {
        let discord_token =
            env::var("DISCORD_TOKEN").expect("DISCORD_TOKEN environment variable required");

        let discord_app_id: u64 = env::var("DISCORD_APP_ID")
            .expect("DISCORD_APP_ID environment variable required")
            .parse()
            .expect("DISCORD_APP_ID must be a valid u64");

        let secret_hex = env::var("BOT_SECRET")
            .expect("BOT_SECRET environment variable required (64 hex chars)");
        let secret_bytes = hex::decode(&secret_hex).expect("BOT_SECRET must be valid hex");
        let bot_secret: [u8; 32] = secret_bytes
            .try_into()
            .expect("BOT_SECRET must be exactly 32 bytes (64 hex chars)");

        let devnet_url = env::var("DEVNET_URL")
            .unwrap_or_else(|_| "https://devnet.pyana.fg-goose.online".to_string());

        let database_url = env::var("DATABASE_URL").unwrap_or_else(|_| "sqlite:bot.db".to_string());

        Self {
            discord_token,
            discord_app_id,
            bot_secret,
            devnet_url,
            database_url,
        }
    }
}
