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

    // ─── Production HTTP read surface (§4.7 Starbridge RemoteRuntime) ─────
    /// Host to bind the axum HTTP read server (e.g. "0.0.0.0" or "127.0.0.1").
    pub http_host: String,
    /// Port for the HTTP read surface (default 8080; choose non-privileged in prod).
    pub http_port: u16,

    // ─── Soft-federation / clique identity (no more hard-coded zero bytes) ─
    /// Federation ID (32 raw bytes) this bot instance participates in.
    /// Loaded from FEDERATION_ID env (64 hex chars) or defaults to all-zero
    /// (suitable only for single-bot dev; real cliques must set the shared root).
    pub federation_id_bytes: [u8; 32],
}

impl Config {
    /// Load configuration from environment variables.
    ///
    /// Returns a friendly error string (for operator UX) instead of panicking
    /// on missing/malformed required vars. This improves the "run the bot"
    /// experience and avoids scary stack traces for common misconfiguration.
    pub fn from_env() -> Result<Self, String> {
        let discord_token = env::var("DISCORD_TOKEN")
            .map_err(|_| "DISCORD_TOKEN environment variable is required (your bot token from Discord developer portal)".to_string())?;

        let app_id_str = env::var("DISCORD_APP_ID")
            .map_err(|_| "DISCORD_APP_ID environment variable is required (the numeric Application ID from Discord developer portal)".to_string())?;
        let discord_app_id: u64 = app_id_str
            .parse()
            .map_err(|_| format!("DISCORD_APP_ID must be a valid u64, got: {}", app_id_str))?;

        let secret_hex = env::var("BOT_SECRET")
            .map_err(|_| "BOT_SECRET environment variable is required (64 hex chars; the 32-byte secret used for deterministic per-user cipherclerk derivation)".to_string())?;
        let secret_bytes =
            hex::decode(&secret_hex).map_err(|e| format!("BOT_SECRET must be valid hex: {}", e))?;
        let bot_secret: [u8; 32] = secret_bytes
            .try_into()
            .map_err(|_| "BOT_SECRET must be exactly 32 bytes (64 hex chars)".to_string())?;

        let devnet_url = env::var("DEVNET_URL")
            .unwrap_or_else(|_| "https://devnet.pyana.fg-goose.online".to_string());

        let database_url = env::var("DATABASE_URL").unwrap_or_else(|_| "sqlite:bot.db".to_string());

        // Production HTTP surface (Starbridge RemoteRuntime / observability)
        let http_host = env::var("HTTP_HOST").unwrap_or_else(|_| "0.0.0.0".to_string());
        let http_port: u16 = env::var("HTTP_PORT")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(8080);

        // Soft-federation root (single Ed25519 trust root for the friend clique).
        // Real deployments MUST supply the 64-hex FEDERATION_ID shared by the clique.
        // Default (all-zero) is only for local dev and single-bot testing.
        let fed_hex = env::var("FEDERATION_ID").unwrap_or_else(|_| "0".repeat(64));
        let fed_bytes_vec = hex::decode(&fed_hex)
            .map_err(|e| format!("FEDERATION_ID must be valid 64-char hex: {}", e))?;
        let federation_id_bytes: [u8; 32] = fed_bytes_vec
            .try_into()
            .map_err(|_| "FEDERATION_ID must decode to exactly 32 bytes".to_string())?;

        if federation_id_bytes.iter().all(|&b| b == 0) {
            // Non-fatal; operator sees in logs when bot starts. Production cliques set the value.
            eprintln!(
                "warning: FEDERATION_ID not set (or all-zero); using dev default. Set FEDERATION_ID=<64 hex> for real soft-federation/clique use."
            );
        }

        Ok(Self {
            discord_token,
            discord_app_id,
            bot_secret,
            devnet_url,
            database_url,
            http_host,
            http_port,
            federation_id_bytes,
        })
    }
}
