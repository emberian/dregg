//! Standalone discharge gateway binary.
//!
//! Usage:
//!   discharge-gateway --config gateway.toml
//!   discharge-gateway --key-hex <64-char-hex> --location https://gateway.example.com
//!
//! See the crate-level docs for the TOML configuration format.

use std::net::SocketAddr;

use clap::Parser;
use tracing::{error, info};

use discharge_gateway_service::{
    ConditionConfig, GatewayConfig, GatewaySettings, build_gateway,
};

#[derive(Parser, Debug)]
#[command(name = "discharge-gateway", about = "Pyana discharge macaroon gateway")]
struct Cli {
    /// Path to TOML configuration file.
    #[arg(short, long)]
    config: Option<String>,

    /// Bind address (overrides config).
    #[arg(long, default_value = "0.0.0.0:8421")]
    bind: String,

    /// Hex-encoded 32-byte shared key (overrides config).
    #[arg(long)]
    key_hex: Option<String>,

    /// Gateway location URL (overrides config).
    #[arg(long)]
    location: Option<String>,

    /// Add an always-allow evaluator (for dev/testing).
    #[arg(long)]
    allow_all: bool,

    /// Rate limit: max discharges per client per hour.
    #[arg(long)]
    rate_limit: Option<u32>,
}

#[tokio::main]
async fn main() {
    tracing_subscriber::fmt()
        .with_env_filter(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| tracing_subscriber::EnvFilter::new("info")),
        )
        .init();

    let cli = Cli::parse();

    let config = match build_config(&cli) {
        Ok(c) => c,
        Err(e) => {
            error!("configuration error: {e}");
            std::process::exit(1);
        }
    };

    let bind_addr: SocketAddr = config.gateway.bind.parse().unwrap_or_else(|e| {
        error!("invalid bind address '{}': {e}", config.gateway.bind);
        std::process::exit(1);
    });

    let (_state, router) = match build_gateway(&config) {
        Ok(r) => r,
        Err(e) => {
            error!("failed to build gateway: {e}");
            std::process::exit(1);
        }
    };

    info!("discharge gateway starting on {}", bind_addr);
    info!("location: {}", config.gateway.location);
    info!(
        "conditions: {}",
        config
            .conditions
            .iter()
            .map(|c| match c {
                ConditionConfig::AlwaysAllow => "always_allow",
                ConditionConfig::RateLimit { .. } => "rate_limit",
                ConditionConfig::Payment { .. } => "payment",
                ConditionConfig::Allowlist { .. } => "allowlist",
                ConditionConfig::ProofRequired => "proof_required",
            })
            .collect::<Vec<_>>()
            .join(", ")
    );

    let listener = tokio::net::TcpListener::bind(bind_addr).await.unwrap_or_else(|e| {
        error!("failed to bind to {}: {e}", bind_addr);
        std::process::exit(1);
    });

    if let Err(e) = axum::serve(listener, router).await {
        error!("server error: {e}");
        std::process::exit(1);
    }
}

fn build_config(cli: &Cli) -> Result<GatewayConfig, String> {
    if let Some(config_path) = &cli.config {
        let contents = std::fs::read_to_string(config_path)
            .map_err(|e| format!("failed to read config '{}': {e}", config_path))?;
        let mut config: GatewayConfig =
            toml::from_str(&contents).map_err(|e| format!("failed to parse TOML: {e}"))?;

        // CLI overrides.
        if let Some(key) = &cli.key_hex {
            config.gateway.signing_key_hex = Some(key.clone());
        }
        if let Some(loc) = &cli.location {
            config.gateway.location = loc.clone();
        }
        config.gateway.bind = cli.bind.clone();

        Ok(config)
    } else {
        // Build config entirely from CLI flags.
        let key_hex = cli.key_hex.clone().ok_or(
            "either --config or --key-hex must be provided",
        )?;
        let location = cli
            .location
            .clone()
            .unwrap_or_else(|| format!("http://{}", cli.bind));

        let mut conditions = Vec::new();
        if cli.allow_all {
            conditions.push(ConditionConfig::AlwaysAllow);
        }
        if let Some(rate) = cli.rate_limit {
            conditions.push(ConditionConfig::RateLimit {
                max_per_hour: rate,
            });
        }

        Ok(GatewayConfig {
            gateway: GatewaySettings {
                bind: cli.bind.clone(),
                signing_key_file: None,
                signing_key_hex: Some(key_hex),
                location,
                discharge_ttl_secs: 300,
            },
            conditions,
        })
    }
}
