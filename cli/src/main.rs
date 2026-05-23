//! `pyana` -- the user-facing CLI for interacting with pyana federation nodes.
//!
//! This tool provides ergonomic commands for inspecting cells, building turns,
//! managing capabilities, and monitoring federation health. It communicates with
//! a running pyana-node over HTTP.

mod commands;
mod config;
mod output;

use clap::{Parser, Subcommand};
use clap_complete::Shell;

use commands::{
    cap, cell, directory, doctor, federation, namespace, node, proof, route, storage, turn, wallet,
};

/// Pyana -- sovereign cell-based compute substrate.
///
/// Interact with cells, turns, capabilities, and federation nodes.
#[derive(Parser)]
#[command(
    name = "pyana",
    version,
    about = "Pyana CLI -- manage cells, turns, capabilities, and federation nodes",
    long_about = None,
    propagate_version = true,
    arg_required_else_help = true,
)]
struct Cli {
    /// Node URL to connect to (overrides config).
    #[arg(long, global = true, env = "PYANA_NODE_URL")]
    node_url: Option<String>,

    /// Output format: color, plain, json.
    #[arg(long, global = true, env = "PYANA_OUTPUT")]
    output: Option<String>,

    /// Path to config file (default: ~/.pyana/config.toml).
    #[arg(long, global = true, env = "PYANA_CONFIG")]
    config: Option<String>,

    /// Enable verbose output (show HTTP request/response details).
    #[arg(long, short, global = true, env = "PYANA_VERBOSE")]
    verbose: bool,

    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Cell inspection and manipulation.
    Cell {
        #[command(subcommand)]
        command: cell::CellCommand,
    },

    /// Turn building and submission.
    Turn {
        #[command(subcommand)]
        command: turn::TurnCommand,
    },

    /// Capability management (export, enliven, handoff).
    Cap {
        #[command(subcommand)]
        command: cap::CapCommand,
    },

    /// Wallet operations (balance, transfer, delegate).
    Wallet {
        #[command(subcommand)]
        command: wallet::WalletCommand,
    },

    /// Node operations (status, connect, sync).
    Node {
        #[command(subcommand)]
        command: node::NodeCommand,
    },

    /// Federation info (constitution, participants, routes).
    Federation {
        #[command(subcommand)]
        command: federation::FederationCommand,
    },

    /// Service mesh (mount, discover, resolve).
    Namespace {
        #[command(subcommand)]
        command: namespace::NamespaceCommand,
    },

    /// Content-addressed storage (read, write, splice, quota).
    Storage {
        #[command(subcommand)]
        command: storage::StorageCommand,
    },

    /// Directory service (structured name resolution, mount/unmount).
    Directory {
        #[command(subcommand)]
        command: directory::DirectoryCommand,
    },

    /// Proof management (verify, inspect, export, IVC chain).
    Proof {
        #[command(subcommand)]
        command: proof::ProofCommand,
    },

    /// DFA route table inspection and amendment.
    Route {
        #[command(subcommand)]
        command: route::RouteCommand,
    },

    /// Check system health (node, wallet, federation, storage).
    Doctor,

    /// Print version information.
    Version,

    /// Generate shell completions.
    Completions {
        /// Shell to generate completions for.
        shell: Shell,
    },

    /// Configuration management.
    Config {
        #[command(subcommand)]
        command: ConfigCommand,
    },
}

#[derive(Subcommand)]
enum ConfigCommand {
    /// Initialize ~/.pyana/config.toml with defaults.
    Init,
    /// Show current configuration.
    Show,
    /// Set a configuration value.
    Set {
        /// Key (dotted path, e.g. "node.url").
        key: String,
        /// Value to set.
        value: String,
    },
}

#[tokio::main]
async fn main() {
    let cli = Cli::parse();

    // Load config, applying CLI overrides.
    let mut cfg = config::Config::load(cli.config.as_deref());
    if let Some(url) = &cli.node_url {
        cfg.node.url = url.clone();
    }
    if let Some(fmt) = &cli.output {
        cfg.output.format = fmt.clone();
    }

    let ctx = output::Context::new(&cfg);

    if cli.verbose {
        eprintln!(
            "{} verbose mode enabled (node: {})",
            console::style("[debug]").dim(),
            cfg.node.url
        );
    }

    let result = match cli.command {
        Commands::Cell { command } => cell::run(command, &cfg, &ctx).await,
        Commands::Turn { command } => turn::run(command, &cfg, &ctx).await,
        Commands::Cap { command } => cap::run(command, &cfg, &ctx).await,
        Commands::Wallet { command } => wallet::run(command, &cfg, &ctx).await,
        Commands::Node { command } => node::run(command, &cfg, &ctx).await,
        Commands::Federation { command } => federation::run(command, &cfg, &ctx).await,
        Commands::Namespace { command } => namespace::run(command, &cfg, &ctx).await,
        Commands::Storage { command } => storage::run(command, &cfg, &ctx).await,
        Commands::Directory { command } => directory::run(command, &cfg, &ctx).await,
        Commands::Proof { command } => proof::run(command, &cfg, &ctx).await,
        Commands::Route { command } => route::run(command, &cfg, &ctx).await,
        Commands::Doctor => doctor::run(&cfg, &ctx).await,
        Commands::Version => {
            print_version(&ctx);
            Ok(())
        }
        Commands::Completions { shell } => {
            let mut cmd = <Cli as clap::CommandFactory>::command();
            clap_complete::generate(shell, &mut cmd, "pyana", &mut std::io::stdout());
            Ok(())
        }
        Commands::Config { command } => run_config(command, &cfg, &ctx),
    };

    if let Err(e) = result {
        ctx.error(&e.to_string());
        std::process::exit(1);
    }
}

fn print_version(ctx: &output::Context) {
    let version = env!("CARGO_PKG_VERSION");
    if ctx.mode == output::Mode::Json {
        let j = serde_json::json!({
            "name": "pyana",
            "version": version,
        });
        ctx.json_stdout(&j);
    } else {
        eprintln!("pyana {}", version);
        eprintln!("  Sovereign cell-based compute substrate CLI");
    }
}

fn run_config(
    cmd: ConfigCommand,
    cfg: &config::Config,
    ctx: &output::Context,
) -> Result<(), Box<dyn std::error::Error>> {
    match cmd {
        ConfigCommand::Init => {
            let path = config::config_path();
            if path.exists() {
                ctx.warn(&format!("Config already exists: {}", path.display()));
                ctx.info("Use `pyana config show` to view, or `pyana config set` to modify.");
                return Ok(());
            }
            config::Config::write_default(&path)?;
            ctx.success(&format!("Initialized config at {}", path.display()));
            Ok(())
        }
        ConfigCommand::Show => {
            let path = config::config_path();
            ctx.header("Configuration");
            ctx.kv("Path", &path.display().to_string());
            ctx.kv("Node URL", &cfg.node.url);
            ctx.kv("Keyfile", &cfg.wallet.keyfile);
            ctx.kv("Output format", &cfg.output.format);
            Ok(())
        }
        ConfigCommand::Set { key, value } => {
            config::set_value(&key, &value)?;
            ctx.success(&format!("Set {key} = {value}"));
            Ok(())
        }
    }
}
