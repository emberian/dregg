//! `dregg-node`: The federation node daemon.
//!
//! This binary runs the backend that:
//! - Hosts an AgentCipherclerk with token management
//! - Participates in federation consensus (attested roots)
//! - Serves a localhost HTTP API for the browser extension cipherclerk
//! - Syncs state with federation peers

mod api;
mod blocklace_sync;
mod catchup;
mod channels_service;
// THE DEOS-HOST (opt-in `deos-host` feature): the node hosts a headless userspace
// deos-js "private server" program. Pulls in mozjs via deos-js, so it is feature-gated.
pub mod config;
mod coord_gate;
#[cfg(feature = "deos-host")]
mod deos_host;
#[cfg(all(test, feature = "deos-host"))]
mod deos_host_e2e;
#[cfg(all(test, feature = "deos-host"))]
mod deos_host_fork_client_e2e;
mod dkg_service;
mod finality_gate;
#[cfg(all(test, feature = "deos-host"))]
mod mud_e2e;
// THE PLAYABLE MUD CLIENT (`dregg-node mud-client`, `deos-host` feature): boots an
// in-process node, hosts the GM (`mud_play_gm.js`), and drops you into a text-MUD REPL
// that drives the living world with real verified turns over the node's HTTP wire.
#[cfg(feature = "deos-host")]
mod mud_client;
#[cfg(all(test, feature = "deos-host"))]
mod mud_client_e2e;
// THE LIVE SHARED WORLD (`deos-host` feature): two distinct identities co-inhabit ONE
// hosted world, each seeing the other's turns LIVE via the node's receipt event stream —
// the first real rung of MULTI-PERSON deos. Headless engine + its co-acting e2e proof.
#[cfg(test)]
mod captp_handoff_e2e;
#[cfg(test)]
mod epoch_transition_e2e;
mod equivocation_court_service;
mod events;
mod execution_cursor;
mod executor_setup;
mod finalization_votes;
mod genesis;
pub mod gossip;
mod identity_export;
#[cfg(test)]
mod mailbox_crank_e2e;
mod mcp;
pub mod metrics;
#[cfg(test)]
mod node_integrator_e2e;
// The operator onboarding dance (gen-validator-key / join / add-validator) — the
// slick, reusable path for folding a node + validator into a federation.
mod operator_join;
mod pg_mirror;
mod prove_pool;
mod relay_service;
mod routing_table;
mod self_cell;
#[cfg(feature = "deos-host")]
mod shared_world;
#[cfg(all(test, feature = "deos-host"))]
mod shared_world_e2e;
mod starbridge_seed;
mod state;
mod storage_service;
mod strand_admission_gate;
#[cfg(feature = "pg-mirror-live")]
mod submit_queue_drainer;
mod trustline_service;
mod turn_proving;
mod ws;

use std::net::{Ipv4Addr, SocketAddr};
use std::path::PathBuf;

use clap::{Parser, Subcommand};
use tracing::{error, info};

#[derive(Parser)]
#[command(name = "dregg-node", about = "Dragon's Egg federation node daemon")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Run the node daemon (HTTP API + federation sync).
    Run {
        /// Port for the localhost HTTP API.
        #[arg(long, default_value = "8420")]
        port: u16,

        /// Bind address for the HTTP API. Defaults to 127.0.0.1 (localhost only).
        /// Use --bind 0.0.0.0 to expose to the network.
        #[arg(long, default_value = "127.0.0.1")]
        bind: String,

        /// Federation peer addresses (host:port), comma-separated.
        #[arg(long, value_delimiter = ',')]
        federation_peers: Vec<String>,

        /// Data directory for persistent state.
        #[arg(long, default_value = "~/.dregg")]
        data_dir: String,

        /// Path to the node key file (relative to data-dir or absolute).
        /// Default: "node.key" in the data directory.
        #[arg(long, default_value = "node.key")]
        key_file: String,

        /// Port for the gossip/federation sync protocol.
        #[arg(long, default_value = "9420")]
        gossip_port: u16,

        #[arg(long, default_value = "0")]
        node_index: usize,

        #[arg(long, default_value = "4")]
        federation_size: usize,

        /// Enable automatic pruning of old blocks/roots below the latest checkpoint.
        /// Off by default (archival mode). Turn on to bound storage growth.
        #[arg(long)]
        enable_pruning: bool,

        /// Prove EVERY finalized turn on the commit path. When set, each
        /// committed turn produces a real full-turn STARK proof and acceptance
        /// is gated on the proof verifying (verify→accept). This is what makes
        /// the public "every state transition is proven" claim TRUE for the
        /// running node. A SPEND turn additionally carries a FRESHNESS-bound
        /// non-revocation leg (no-double-spend bindings (a)+(b) fire via
        /// `verify_full_turn_bound`). Off by default (full proving is on the hot
        /// path); the devnet enables it. Can also be enabled via
        /// `DREGG_PROVE_TURNS=1`.
        ///
        /// AUDIT-GRADE DEVNET: a preproduction node "worthy of audit" MUST run
        /// with `--prove-turns` (or `DREGG_PROVE_TURNS=1`) so committed turns are
        /// proven and a light client can fetch them via
        /// `GET /api/turn/{hash}/proof` and re-verify (spend turns against the
        /// canonical revocation root).
        #[arg(long)]
        prove_turns: bool,

        /// Checkpoint interval in blocks (default: 1000).
        #[arg(long, default_value = "1000")]
        checkpoint_interval: u64,

        /// Blocklace consensus tuning (safe defaults match historical behavior).
        /// These remove "wrong way" hard-coded consts and let operators tune
        /// for devnet (aggressive/fast) vs production (conservative) without
        /// recompiles. Blocklace is the default engine when peers or full mode.
        /// Disable path: solo + no peers (or future --solo-only).

        /// Blocklace checkpoint interval in finalized blocks (default 100, matches devnet genesis).
        #[arg(long, default_value = "100")]
        blocklace_checkpoint_interval: u64,

        /// Blocklace constitution wave timeout in milliseconds (default 10000).
        #[arg(long, default_value = "10000")]
        blocklace_wave_timeout_ms: u64,

        /// Block production CHECK interval in milliseconds. Block production is
        /// mutation-driven: on each check tick the node produces a block only
        /// when there are pending queued turns, a reactive ack owed for
        /// received peer blocks, or the idle-heartbeat window has expired (see
        /// --idle-heartbeat-ms). Most ticks produce nothing — an idle node no
        /// longer emits an empty block per tick. Set 0 to disable the cadence
        /// task entirely (purely quiescent: blocks only on turn submission).
        /// Default 2000ms (bounds turn-drain / reactive-ack latency).
        #[arg(long, default_value = "1000")]
        block_cadence_ms: u64,

        /// Idle heartbeat interval in milliseconds. When the node has produced
        /// no block at all for this long, it emits ONE empty heartbeat block
        /// (a real, signed block linking the current tips) so liveness and
        /// finality probes still advance while idle. Set 0 to disable idle
        /// heartbeats. Also configurable via the DREGG_IDLE_HEARTBEAT_MS env
        /// var (the env var wins when set). Default 120000 (2 minutes).
        #[arg(long, default_value = "120000")]
        idle_heartbeat_ms: u64,

        /// Minimum interval in milliseconds between THIS node's blocks on the
        /// multi-party (n>1) round-driven path — the quiescent-on-demand rate
        /// cap. The node emits at most one block per this interval: turns are
        /// batched within the window and each consensus wave is closed across a
        /// few interval-spaced rounds. Independent of --block-cadence-ms (which is
        /// only the CHECK interval) and of turn submission. Also configurable via
        /// the DREGG_MIN_BLOCK_INTERVAL_MS env var (the env var wins when set).
        ///
        /// Default 1000 (≤ one block / 1s). The cap is a SPAM floor, not the
        /// pacer: round advancement is already gated by the cohort rule
        /// (`plan_round_block` needs a supermajority of distinct creators at the
        /// current round), so the committee never outruns its slowest honest
        /// member regardless of this value — the cap only prevents a degenerate
        /// empty-block burst. The old 5000ms default made finality artificially
        /// slow: closing one wave took ~5 interval-spaced rounds ≈ 25-30s, so a
        /// committee under sustained turn load could not finalize turn-after-turn
        /// inside a reasonable window (the live n=4 stalled on this). At 1000ms a
        /// wave closes in a few seconds while the idle DAG still stays quiet (the
        /// 2s idle-heartbeat floor governs quiescence, not this cap).
        #[arg(long, default_value = "2000")]
        min_block_interval_ms: u64,

        /// Enable the faucet endpoint (POST /api/faucet).
        /// Only suitable for devnets. Allows anyone to request computrons from the
        /// genesis faucet cell.
        #[arg(long)]
        enable_faucet: bool,

        /// Federation mode: "solo" for single-node devnet (default), "full" for BFT quorum.
        ///
        /// In solo mode, the node processes turns immediately without waiting for peers,
        /// skips gossip/consensus, produces Tentative receipts, and uses a local
        /// NullifierLog for sequencing. When peers are detected (via gossip), the node
        /// can auto-upgrade to full mode.
        #[arg(long, default_value = "solo")]
        federation_mode: String,

        ///
        /// "blocklace" uses the Cordial Miners blocklace for quiescent, leaderless
        /// DAG-based BFT consensus with the tau total ordering function.
        #[arg(long, default_value = "blocklace")]
        consensus: String,

        /// Reference groups to join (comma-separated group ID hex strings).
        /// When specified, the node participates in multiple groups simultaneously
        /// using cross-reference dissemination (Phase C) instead of the legacy
        /// bridge relay pattern. Each group ID is a 64-character hex string.
        #[arg(long, value_delimiter = ',')]
        groups: Vec<String>,

        /// (Dangerous) Auto-approve all federation join proposals received via
        /// gossip. F-CRIT-2: if true, ANY peer that publishes a
        /// `MembershipAction::Join` block causes this node to cast an Approve
        /// vote, which combined with the (n*2/3)+1 BFT threshold can flip the
        /// federation. Default: false. Devnet (`.devnet` marker file) implicitly
        /// enables this.
        #[arg(long)]
        auto_approve_joins: bool,

        /// Extra CORS origins to allow cross-origin browser access, e.g.
        /// `https://devnet.example.com`. Repeat the flag or pass a
        /// comma-separated list. localhost / 127.0.0.1 / [::1] and browser
        /// extensions are ALWAYS allowed; this only widens the allowlist for a
        /// deployed site origin. Also reads `DREGG_CORS_ORIGINS` (comma-
        /// separated) and unions it with these flags. Default: empty
        /// (locked down to localhost + extensions). Not needed when the site
        /// and node are served same-origin behind one reverse proxy (see
        /// deploy/aws/caddy/Caddyfile).
        ///
        /// F-1 (rate-limit proxy bypass): when the node runs behind a reverse
        /// proxy, set `DREGG_TRUSTED_PROXIES` (comma-separated proxy IPs) so the
        /// per-client rate limiter keys on the real `X-Forwarded-For` client IP
        /// instead of collapsing every request into one global bucket. The
        /// header is honored ONLY from these trusted peers; a directly-exposed
        /// node should leave it unset (default) so XFF is never believed.
        #[arg(long = "cors-origin", value_delimiter = ',')]
        cors_origins: Vec<String>,

        /// THE DEOS-HOST (`deos-host` feature): host a headless userspace deos-js
        /// "private server" program at this path. On boot the node mints the server
        /// cell, runs the program's setup (which registers cap-gated affordances +
        /// spawns cells via `deos.server.*`), and publishes the affordance surface for
        /// client discovery at `GET /api/server/{cell}/affordances`. With the feature
        /// off this flag is accepted but inert (the node logs a warning).
        #[arg(long = "deos-program")]
        deos_program: Option<String>,
    },

    /// Initialize the data directory and generate a node keypair.
    Init {
        /// Data directory to initialize.
        #[arg(long, default_value = "~/.dregg")]
        data_dir: String,
    },

    /// Check if the node is running and show sync state.
    Status {
        /// Port to check (default: 8420).
        #[arg(long, default_value = "8420")]
        port: u16,
    },

    /// PLAY the node-hosted MUD: boot a self-contained living world (an in-process
    /// headless node hosting the GM `mud_play_gm.js`) and drop into an interactive
    /// text-MUD loop. Every `look` reads the real ledger; every `move` / `gain-xp` /
    /// `descend` is a real signed, verified turn committed on the node — and a forbidden
    /// GM-only write is refused (the asymmetry). Requires the `deos-host` feature.
    MudClient {
        /// Seed deriving the player identity (same seed → same character across runs).
        #[arg(long, default_value = "mud-play-aria")]
        player_seed: String,
    },

    /// Run as an MCP (Model Context Protocol) server over stdio.
    ///
    /// Reads JSON-RPC from stdin and writes responses to stdout.
    /// Used by AI assistants (Claude, GPT, etc.) to interact with the node.
    Mcp {
        /// Data directory for persistent state.
        #[arg(long, default_value = "~/.dregg")]
        data_dir: String,

        /// Federation peer addresses (host:port), comma-separated.
        #[arg(long, value_delimiter = ',')]
        federation_peers: Vec<String>,
    },

    /// Register a peer federation's committee descriptor in this node's
    /// `known_federations/` directory.
    ///
    /// This is the out-of-band cross-federation trust setup step from
    /// `SILVER-VISION-E2E-VERIFICATION.md` §0.2. The operator copies the
    /// peer federation's `genesis.json` (or `federation_descriptor.json`)
    /// into a known path and runs this command so the local node accepts
    /// the peer's signed attestations / federation receipts.
    ///
    /// On success the descriptor is canonicalised and written to
    /// `<data-dir>/known_federations/<federation_id>.json`.
    RegisterFederation {
        /// Local data directory.
        #[arg(long, default_value = "~/.dregg")]
        data_dir: String,
        /// Path to the peer federation's descriptor JSON. The file must
        /// have the same shape as `genesis.json` (federation_id +
        /// committee_epoch + threshold + validators[].public_key) — i.e.
        /// what `dregg-node genesis` already produces.
        #[arg(long)]
        descriptor: PathBuf,
    },

    /// Generate devnet genesis configuration (keys, genesis.json, env files).
    Genesis {
        /// Number of validator nodes to generate keys for.
        #[arg(long, default_value = "4")]
        validators: usize,

        /// Epoch length in blocks.
        #[arg(long, default_value = "1000")]
        epoch_length: u64,

        /// Checkpoint interval in blocks.
        #[arg(long, default_value = "100")]
        checkpoint_interval: u64,

        /// Output directory for the generated configuration.
        #[arg(long, default_value = "./devnet-config")]
        output: PathBuf,
    },

    /// Run as a hosted inbox relay operator.
    ///
    /// Starts an HTTP server that accepts CapTP store-and-forward messages,
    /// hosts inboxes for subscribed users, charges deposits, bonds computrons,
    /// runs periodic GC, and exposes status/monitoring endpoints.
    Relay {
        /// Port for the relay HTTP API.
        #[arg(long, default_value = "3100")]
        port: u16,

        /// Bond amount in computrons (operator stake).
        #[arg(long, default_value = "10000")]
        bond: u64,

        /// Maximum total inbox capacity to host.
        #[arg(long, default_value = "100000")]
        max_capacity: usize,

        /// GC interval in seconds.
        #[arg(long, default_value = "300")]
        gc_interval: u64,

        /// Message TTL in blocks (messages older than this are GC'd).
        #[arg(long, default_value = "1000")]
        message_ttl: u64,

        /// Max delivery latency (SLA) in blocks.
        #[arg(long, default_value = "50")]
        max_delivery_latency: u64,

        /// Path for persistent relay state file.
        #[arg(long, default_value = "./relay-state.json")]
        state_file: PathBuf,

        /// Data directory (for reading operator key).
        #[arg(long, default_value = "~/.dregg")]
        data_dir: String,

        /// Default inbox capacity for new subscriptions.
        #[arg(long, default_value = "100")]
        default_inbox_capacity: usize,

        /// Default minimum deposit for new inboxes.
        #[arg(long, default_value = "100")]
        default_min_deposit: u64,

        /// Minimum deposit per message (computrons).
        #[arg(long, default_value = "100")]
        min_message_deposit: u64,

        /// One-time subscription fee for creating an inbox.
        #[arg(long, default_value = "1000")]
        subscription_fee: u64,
    },

    /// Generate (or read) this box's validator keypair and print its PUBLIC key.
    ///
    /// Idempotent — if `node.key` already exists in the data dir, its public key
    /// is read and printed; otherwise a fresh 32-byte seed is generated (0600).
    /// Hand the printed PUBLIC key to the federation operator; they admit you
    /// with `dregg-node add-validator --pubkey <it>` and send back the resulting
    /// genesis.json for `dregg-node join`.
    GenValidatorKey {
        /// Data directory holding (or to hold) `node.key`.
        #[arg(long, default_value = "~/.dregg")]
        data_dir: String,
        /// Emit JSON (`{public_key, key_file, generated}`).
        #[arg(long)]
        json: bool,
    },

    /// Join a federation: peer to a bootstrap node, sync the blocklace, run as a
    /// follower (or, if this node's key is in the committee, a voting validator).
    ///
    /// Pre-flights the data dir (auto-generates `node.key` if absent, printing the
    /// pubkey) and requires a committee `genesis.json` to be present — a node
    /// cannot verify a federation's blocks without its committee descriptor, so
    /// `join` refuses rather than trusting nobody. The node then catches up the
    /// DAG from the bootstrap and, if it is NOT yet a committee member,
    /// auto-proposes membership (`propose_join_if_needed`) and follows until an
    /// operator admits it via `add-validator`.
    Join {
        /// Bootstrap peer to dial: `host:gossip_port` (e.g. 100.64.0.1:9420).
        /// One live peer is enough; gossip-of-peers fills in the rest.
        #[arg(long)]
        bootstrap: String,
        /// Data directory (must hold, or will receive, `node.key` + `genesis.json`).
        #[arg(long, default_value = "~/.dregg")]
        data_dir: String,
        /// Localhost/overlay HTTP read-API port.
        #[arg(long, default_value = "8420")]
        port: u16,
        /// Bind address for the read API. Default 127.0.0.1 (loopback-only).
        /// Bind the OVERLAY ip (e.g. 100.64.0.2) so authorized peers can sync —
        /// NOT 0.0.0.0 (that exposes every interface, red-team MESH-2).
        #[arg(long, default_value = "127.0.0.1")]
        bind: String,
        /// Gossip/federation sync port (QUIC, UDP).
        #[arg(long, default_value = "9420")]
        gossip_port: u16,
        /// Prove every finalized turn on the commit path (audit-grade).
        #[arg(long)]
        prove_turns: bool,
        /// Enable the devnet faucet endpoint.
        #[arg(long)]
        enable_faucet: bool,
        /// (Devnet) auto-approve incoming join proposals.
        #[arg(long)]
        auto_approve_joins: bool,
    },

    /// Add one or more validators to this node's committee (the authority op).
    ///
    /// Reads `genesis.json` from the data dir, folds the given pubkey(s) into the
    /// committee, recomputes the `federation_id` + BFT `threshold`
    /// (`quorum_threshold`), and writes the new committee descriptor back (plus a
    /// content-named `genesis-<id8>.json` to distribute). Filesystem access to
    /// the node's data dir IS the authority — there is no remote self-admit (that
    /// would defeat BFT). The re-roll changes the `federation_id`, so distribute
    /// the new genesis.json to every committee node and restart into full mode.
    AddValidator {
        /// Validator public key(s) to add (64-hex Ed25519). Repeat for several.
        #[arg(long = "pubkey", required = true)]
        pubkeys: Vec<String>,
        /// Data directory holding the committee `genesis.json`.
        #[arg(long, default_value = "~/.dregg")]
        data_dir: String,
        /// Emit JSON.
        #[arg(long)]
        json: bool,
    },

    /// LIVE validator-set reconfiguration on a RUNNING node (the chain-continuing
    /// path — no genesis re-roll, no fresh chain, no federation_id change).
    ///
    /// Submits an on-chain membership proposal to a running node's API: `--add`
    /// proposes a Join, `--remove` proposes a Leave, `--rotate <old> <new>` is a
    /// remove-then-add. The change only APPLIES once a quorum of the CURRENT
    /// committee ratifies it through finality — proposing is not authority, the
    /// committee's votes are. Unlike the offline `add-validator` (which re-rolls
    /// genesis and requires a coordinated restart), this is a live operation: the
    /// new validator joins via `join --bootstrap`, syncs, and votes from the new
    /// epoch while the chain keeps advancing.
    ProposeEpochTransition {
        /// Validator pubkey(s) to ADD (64-hex Ed25519). Repeat for several.
        #[arg(long = "add")]
        add: Vec<String>,
        /// Validator pubkey(s) to REMOVE (64-hex Ed25519). Repeat for several.
        #[arg(long = "remove")]
        remove: Vec<String>,
        /// Rotate one validator for another: `--rotate <old_pubkey> <new_pubkey>`
        /// (desugars to remove(old) + add(new)).
        #[arg(long = "rotate", num_args = 2, value_names = ["OLD", "NEW"])]
        rotate: Vec<String>,
        /// Running node's HTTP API port.
        #[arg(long, default_value = "8420")]
        port: u16,
        /// Bearer token for the node API (if the node has a passphrase set). On a
        /// loopback devnet node with no passphrase this can be omitted.
        #[arg(long)]
        token: Option<String>,
        /// Emit JSON.
        #[arg(long)]
        json: bool,
    },
}

#[tokio::main]
async fn main() {
    // Install the ring CryptoProvider for rustls (required by quinn/QUIC).
    rustls::crypto::ring::default_provider()
        .install_default()
        .expect("failed to install rustls CryptoProvider");

    // Arm the verified-Lean distributed coordination gates (coord / captp / federation / intent).
    // These crates are FFI-free and route their verified decisions through their `verified_gate`
    // seams; this installs the Lean-backed impls from `dregg-exec-lean` (the single FFI boundary)
    // once at startup. On an FFI-free target this crate isn't depended on at all and the native-Rust
    // differential siblings decide.
    dregg_exec_lean::register_distributed_gates();

    // Initialize tracing. Write to stderr so the MCP stdio subcommand (which
    // serves JSON-RPC on stdout) doesn't get corrupted by log lines.
    tracing_subscriber::fmt()
        .with_writer(std::io::stderr)
        .with_env_filter(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| "dregg_node=info".into()),
        )
        .init();

    let cli = Cli::parse();

    match cli.command {
        Command::Run {
            port,
            bind,
            federation_peers,
            data_dir,
            key_file,
            gossip_port,
            node_index,
            federation_size,
            enable_pruning,
            prove_turns,
            checkpoint_interval,
            blocklace_checkpoint_interval,
            blocklace_wave_timeout_ms,
            block_cadence_ms,
            idle_heartbeat_ms,
            min_block_interval_ms,
            enable_faucet,
            federation_mode,
            consensus,
            groups,
            auto_approve_joins,
            cors_origins,
            deos_program,
        } => {
            run_node(
                port,
                &bind,
                federation_peers,
                &data_dir,
                &key_file,
                gossip_port,
                node_index,
                federation_size,
                enable_pruning,
                prove_turns,
                checkpoint_interval,
                blocklace_checkpoint_interval,
                blocklace_wave_timeout_ms,
                block_cadence_ms,
                idle_heartbeat_ms,
                min_block_interval_ms,
                enable_faucet,
                &federation_mode,
                &consensus,
                groups,
                auto_approve_joins,
                cors_origins,
                deos_program,
            )
            .await
        }
        Command::Init { data_dir } => init_node(&data_dir),
        Command::Status { port } => check_status(port).await,
        Command::MudClient { player_seed } => {
            #[cfg(feature = "deos-host")]
            {
                mud_client::play_interactive(&player_seed).await;
            }
            #[cfg(not(feature = "deos-host"))]
            {
                let _ = player_seed;
                eprintln!(
                    "`mud-client` requires the `deos-host` feature (it hosts a deos-js GM). \
                     Rebuild with `cargo run --features deos-host --bin dregg-node -- mud-client`."
                );
                std::process::exit(1);
            }
        }
        Command::Mcp {
            data_dir,
            federation_peers,
        } => run_mcp(&data_dir, federation_peers).await,
        Command::Genesis {
            validators,
            epoch_length,
            checkpoint_interval,
            output,
        } => genesis::run_genesis(validators, epoch_length, checkpoint_interval, &output),
        Command::RegisterFederation {
            data_dir,
            descriptor,
        } => run_register_federation(&data_dir, &descriptor),
        Command::Relay {
            port,
            bond,
            max_capacity,
            gc_interval,
            message_ttl,
            max_delivery_latency,
            state_file,
            data_dir,
            default_inbox_capacity,
            default_min_deposit,
            min_message_deposit,
            subscription_fee,
        } => {
            run_relay(
                port,
                bond,
                max_capacity,
                gc_interval,
                message_ttl,
                max_delivery_latency,
                state_file,
                &data_dir,
                default_inbox_capacity,
                default_min_deposit,
                min_message_deposit,
                subscription_fee,
            )
            .await
        }
        Command::GenValidatorKey { data_dir, json } => {
            if let Err(e) = operator_join::gen_validator_key(&data_dir, json) {
                eprintln!("error: {e}");
                std::process::exit(1);
            }
        }
        Command::AddValidator {
            pubkeys,
            data_dir,
            json,
        } => {
            if let Err(e) = operator_join::add_validator(&data_dir, &pubkeys, json) {
                eprintln!("error: {e}");
                std::process::exit(1);
            }
        }
        Command::ProposeEpochTransition {
            mut add,
            mut remove,
            rotate,
            port,
            token,
            json,
        } => {
            // `--rotate OLD NEW` desugars to remove(OLD) + add(NEW).
            if rotate.len() == 2 {
                remove.push(rotate[0].clone());
                add.push(rotate[1].clone());
            }
            if let Err(e) =
                operator_join::propose_epoch_transition(port, token.as_deref(), &add, &remove, json)
                    .await
            {
                eprintln!("error: {e}");
                std::process::exit(1);
            }
        }
        Command::Join {
            bootstrap,
            data_dir,
            port,
            bind,
            gossip_port,
            prove_turns,
            enable_faucet,
            auto_approve_joins,
        } => {
            // Pre-flight: ensure key + committee descriptor, report membership.
            let plan = match operator_join::prepare_join(&data_dir, &bootstrap, false) {
                Ok(p) => p,
                Err(e) => {
                    eprintln!("error: {e}");
                    std::process::exit(1);
                }
            };
            operator_join::announce_join(&plan, &data_dir, &bind);
            // Start the daemon in full (BFT-quorum) mode, peered to the bootstrap.
            // The blocklace catches up from the peer; a non-member auto-proposes
            // membership (see `blocklace_sync::propose_join_if_needed`).
            run_node(
                port,
                &bind,
                vec![plan.bootstrap.clone()],
                &data_dir,
                "node.key",
                gossip_port,
                0,
                0,
                false,
                prove_turns,
                1000,
                100,
                10000,
                2000,
                120000,
                5000,
                enable_faucet,
                "full",
                "blocklace",
                Vec::new(),
                auto_approve_joins,
                Vec::new(),
                None,
            )
            .await
        }
    }
}

/// Run the node: start HTTP API server and federation sync.
#[allow(clippy::too_many_arguments)]
async fn run_node(
    port: u16,
    bind: &str,
    peers: Vec<String>,
    data_dir: &str,
    key_file: &str,
    gossip_port: u16,
    _node_index: usize,
    _federation_size: usize,
    enable_pruning: bool,
    prove_turns: bool,
    checkpoint_interval: u64,
    blocklace_checkpoint_interval: u64,
    blocklace_wave_timeout_ms: u64,
    block_cadence_ms: u64,
    idle_heartbeat_ms: u64,
    min_block_interval_ms: u64,
    enable_faucet: bool,
    federation_mode_str: &str,
    consensus_engine: &str,
    groups: Vec<String>,
    auto_approve_joins_flag: bool,
    cors_origins_flag: Vec<String>,
    deos_program: Option<String>,
) {
    let data_path = expand_path(data_dir);

    if !data_path.exists() {
        error!(
            "data directory does not exist: {}. Run `dregg-node init` first.",
            data_path.display()
        );
        std::process::exit(1);
    }

    // devnet *mode* is LIVE: `Genesis` config-gen, `--enable-faucet`, and the `.devnet`
    // marker below are first-class local-devnet plumbing (NOT the decommissioned hosted
    // devnet, which is gone). Do not strip this mode thinking it's dead.
    // Check for `.devnet` marker and warn prominently.
    if data_path.join(".devnet").exists() {
        tracing::warn!("Running in DEVNET mode \u{2014} keys are not production-grade");
    }

    // Initialize node state with configurable key file.
    let has_peers = !peers.is_empty();
    let node_state = match state::NodeState::new_with_key_file(&data_path, peers, key_file) {
        Ok(s) => s,
        Err(e) => {
            error!("failed to initialize node state: {e}");
            std::process::exit(1);
        }
    };

    // F-DOS-1: start the async STARK prove pool so the submit/commit handlers
    // offload full proving OFF the global state-write lock (they revalidate the
    // witness inline — FRI-free, sub-ms — and return a fast Tentative ack).
    {
        let pool = prove_pool::ProvePool::spawn(node_state.clone());
        node_state.set_prove_pool(pool).await;
    }

    // Load genesis.json if present in the data directory.
    let mut starbridge_seeded_from_genesis = false;
    let genesis_path = data_path.join("genesis.json");
    if genesis_path.exists() {
        match std::fs::read_to_string(&genesis_path) {
            Ok(json_str) => {
                match serde_json::from_str::<serde_json::Value>(&json_str) {
                    Ok(genesis) => {
                        let mut s = node_state.write().await;
                        // Set committee_epoch BEFORE loading keys so the
                        // first federation_id derivation uses the correct
                        // epoch.
                        if let Some(ce) = genesis["committee_epoch"].as_u64() {
                            s.committee_epoch = ce;
                        }
                        // Extract validator public keys from genesis.
                        if let Some(validators) = genesis["validators"].as_array() {
                            let mut fed_keys = Vec::new();
                            for v in validators {
                                if let Some(pk_hex) = v["public_key"].as_str()
                                    && let Some(pk_bytes) = hex_decode_32(pk_hex)
                                {
                                    fed_keys.push(dregg_types::PublicKey(pk_bytes));
                                }
                            }
                            if !fed_keys.is_empty() {
                                info!(
                                    key_count = fed_keys.len(),
                                    "loaded federation keys from genesis.json"
                                );
                                s.set_federation_keys(fed_keys);
                            }
                        }
                        // Verify the genesis-declared federation_id matches the
                        // committee-derived id (audit F1: the writer of
                        // genesis.json doesn't get to pick an arbitrary id).
                        if let Some(declared_id) = genesis["federation_id"].as_str() {
                            let derived = dregg_types::hex_encode(&s.federation_id);
                            if declared_id != derived {
                                tracing::warn!(
                                    declared = %declared_id,
                                    derived = %derived,
                                    "genesis.json federation_id does not match committee-derived id (audit F1); using derived id",
                                );
                            }
                        }
                        // Extract threshold from genesis.
                        if let Some(threshold) = genesis["threshold"].as_u64() {
                            s.decryption_threshold = threshold as usize;
                        }
                        // Extract checkpoint interval from genesis.
                        if let Some(ci) = genesis["checkpoint_interval"].as_u64() {
                            s.checkpoint_interval = ci;
                        }
                        // Recovery ordering (the issuer-well fix): reconstruct
                        // the genesis BASELINE first on a fresh ledger (the
                        // `genesis_moves` replay EXACTLY ONCE over value-empty
                        // cells), THEN re-apply the recovered commit-log overlay
                        // so every bot-touched cell's FINALIZED post-state wins.
                        // The old order (genesis reseed applied OVER the overlay)
                        // re-credited every move RECIPIENT already in the overlay
                        // — a double-credit that diverged the reconstructed root.
                        let cell_load = reseed_genesis_then_overlay(&genesis, &mut s.ledger);
                        if cell_load.total() > 0 {
                            info!(
                                inserted = cell_load.inserted,
                                existing = cell_load.existing,
                                skipped = cell_load.skipped,
                                invalid = cell_load.invalid,
                                "processed genesis initial_cells"
                            );
                        }
                        // THE EPOCH §5: pick up the genesis wells so every
                        // executor (configure_turn_executor) runs fees and
                        // burns as exact MOVES.
                        if let Some(fee_well_hex) = genesis["fee_well"].as_str() {
                            match hex_decode_32(fee_well_hex) {
                                Some(id) => s.fee_well = Some(dregg_cell::CellId(id)),
                                None => tracing::warn!(
                                    "genesis fee_well is not a 32-byte hex cell id; fees will burn"
                                ),
                            }
                        }
                        if let Some(issuer_well_hex) = genesis["issuer_well"].as_str() {
                            match hex_decode_32(issuer_well_hex) {
                                // The devnet issuer well backs the DEFAULT
                                // asset (all-zero token domain).
                                Some(id) => {
                                    s.issuer_wells.push(([0u8; 32], dregg_cell::CellId(id)))
                                }
                                None => tracing::warn!(
                                    "genesis issuer_well is not a 32-byte hex cell id; burns stay non-conserving"
                                ),
                            }
                        }
                        let federation_id = s.federation_id;
                        let operator_pubkey = s.cclerk.public_key().0;
                        let seed_stats =
                            starbridge_seed::seed_starbridge_factory_cells_with_operator(
                                &genesis,
                                &data_path,
                                &mut s.ledger,
                                federation_id,
                                Some(operator_pubkey),
                            );
                        if seed_stats.total() > 0 {
                            starbridge_seeded_from_genesis = true;
                            info!(
                                registered = seed_stats.registered_factories,
                                created = seed_stats.created,
                                existing = seed_stats.existing,
                                skipped = seed_stats.skipped,
                                failed = seed_stats.failed,
                                "processed genesis starbridge_cells"
                            );
                        }
                        info!(genesis = %genesis_path.display(), "genesis configuration loaded");
                    }
                    Err(e) => {
                        error!(error = %e, "failed to parse genesis.json");
                    }
                }
            }
            Err(e) => {
                error!(error = %e, "failed to read genesis.json");
            }
        }
    }

    // Starbridge devnet backfill — idempotent on every boot. A devnet data dir
    // that predates the starbridge seed (no genesis.json at all, or one without
    // `starbridge_cells`) gains the default poll/bounty/nameservice/... factory
    // cells on restart, insert-if-absent exactly like `materialize_genesis_cells`.
    // Gated on `--enable-faucet` (the explicit devnet switch); production nodes
    // seed only through genesis.
    if enable_faucet && !starbridge_seeded_from_genesis {
        let mut s = node_state.write().await;
        let federation_id = s.federation_id;
        let operator_pubkey = s.cclerk.public_key().0;
        let stats = starbridge_seed::seed_default_starbridge_cells_devnet(
            &data_path,
            &mut s.ledger,
            federation_id,
            Some(operator_pubkey),
        );
        if stats.total() > 0 {
            info!(
                registered = stats.registered_factories,
                created = stats.created,
                existing = stats.existing,
                skipped = stats.skipped,
                failed = stats.failed,
                "starbridge devnet backfill seeding complete (default cell set)"
            );
        }
    }

    // Recovery-convergence verdict (DEFERRED from NodeState construction). The
    // genesis/baseline cells are now (re)seeded on top of the recovered
    // commit-log overlay, so the in-memory ledger is the FULL finalized ledger
    // (genesis ⊕ touched). Verify its canonical root equals the durably recorded
    // finalized root. A node that finalized turns BELOW the first ledger
    // checkpoint converges HERE (the genesis baseline restores the untouched
    // cells the overlay can't carry) — it no longer fail-closes on a clean
    // restart. A genuinely corrupt/divergent store STILL fails closed: reseeding
    // is insert-if-absent and cannot paper over a tampered touched cell. FAIL
    // CLOSED on mismatch — refuse to serve wrong state.
    if let Err(e) = node_state.verify_recovery_convergence().await {
        error!("{e}");
        std::process::exit(1);
    }

    // Load known federations from disk so cross-federation receipt verification
    // can route through the unified registry on startup.
    {
        let mut s = node_state.write().await;
        match s.load_known_federations(&data_path) {
            Ok(0) => {}
            Ok(n) => info!(count = n, "loaded peer federations from known_federations/"),
            Err(e) => tracing::warn!(error = %e, "failed to load known_federations"),
        }
    }

    // Parse federation mode from CLI flag. "solo" is shorthand for a
    // committee-of-one federation; "full" turns BFT quorum on. Per
    // FEDERATION-UNIFICATION-DESIGN.md §5, "solo" is no longer a separate
    // runtime mode — it just configures threshold=1 and skips peer gossip.
    let mut is_solo_mode = match federation_mode_str.to_lowercase().as_str() {
        "solo" => true,
        "full" => false,
        other => {
            error!("invalid --federation-mode value: '{other}'; defaulting to solo");
            true
        }
    };

    // Configure pruning and solo state.
    {
        let mut s = node_state.write().await;
        s.pruning_enabled = enable_pruning;
        s.checkpoint_interval = checkpoint_interval;

        // Full-turn proving on the commit path (--prove-turns or
        // DREGG_PROVE_TURNS=1, devnet). When enabled, every finalized turn is
        // proven + verify-gated; see `turn_proving::prove_and_verify_finalized_turn`.
        let prove_turns_env = std::env::var("DREGG_PROVE_TURNS")
            .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
            .unwrap_or(false);
        s.full_turn_proving_enabled = prove_turns || prove_turns_env;
        if s.full_turn_proving_enabled {
            info!(
                "full-turn proving ENABLED: every committed turn produces a \
                 verified full-turn STARK proof on the commit path"
            );
        }

        // AUTO-UPGRADE: a node configured solo but with PEERS present (a peer
        // list and/or a multi-key federation committee from genesis) should NOT
        // sit silently solo — that is the "configured solo, never federates"
        // footgun. Peer-presence drives the mode: detecting >1 committee member
        // or any configured peer upgrades the node out of solo into full
        // (BFT-quorum) operation, with a loud warning so the operator sees it.
        let committee_size = s.known_federation_keys.len();
        let peers_present = has_peers || committee_size > 1;
        if solo_should_auto_upgrade(is_solo_mode, has_peers, committee_size) {
            tracing::warn!(
                peers = has_peers,
                committee_size,
                "configured --federation-mode solo but PEERS are present (peer list and/or a \
                 multi-member genesis committee) — AUTO-UPGRADING to full (BFT-quorum) mode so \
                 this node actually federates instead of sitting solo. Pass --federation-mode \
                 full explicitly to silence this, or run with no peers for a genuine solo node."
            );
            is_solo_mode = false;
        }

        // In solo mode, initialize the SoloConsensusState with the node's signing key.
        if is_solo_mode {
            let signing_key = s.cclerk.gossip_signing_key().to_bytes();
            s.solo_consensus = Some(dregg_federation::solo::SoloConsensusState::new(signing_key));
            info!("federation mode: solo (committee of one) — no quorum required");
        } else {
            info!(
                peers_present,
                committee_size, "federation mode: full — BFT quorum required for finality"
            );
        }
    }

    // ── MARSHAL-ONLY STARTUP TRIPWIRE (fail-CLOSED refusal) ───────────────────
    // A binary linked WITHOUT the verified Lean executor archive (libdregg_lean.a)
    // runs the UN-verified Rust executor: `dregg_lean_ffi::lean_available()` is false.
    // Such a build must NEVER deploy silently as if it were the verified node — a
    // stale or gitignored Lean seed degrades the whole executor to marshal-only with
    // no other visible signal. Historically this tripwire was LOG-ONLY (an `error!`),
    // so a *solo* node whose logs were ignored could still serve its API presenting as
    // verified. It is now fail-CLOSED: any node (solo OR full) REFUSES to start
    // (`exit(1)`) when the verified executor is not linked, UNLESS the operator
    // explicitly accepts the un-verified executor with `DREGG_ALLOW_UNVERIFIED_CONSENSUS=1`
    // (the same escape hatch the verified-consensus hard-check below uses). This makes an
    // unverified node a DELIBERATE opt-in, never a silent default. (See
    // docs/BUILD-LEAN-LINKED-NODE.md.)
    let lean_available = dregg_lean_ffi::lean_available();
    let allow_unverified = env_allow_unverified(
        std::env::var("DREGG_ALLOW_UNVERIFIED_CONSENSUS")
            .ok()
            .as_deref(),
    );
    if !lean_available {
        if !marshal_only_must_refuse(lean_available, allow_unverified) {
            tracing::warn!(
                "MARSHAL-ONLY BUILD OVERRIDDEN: `dregg_lean_ffi::lean_available()` is false — this \
                 binary was linked WITHOUT the verified Lean executor archive (libdregg_lean.a) and \
                 is running the UN-VERIFIED Rust executor. DREGG_ALLOW_UNVERIFIED_CONSENSUS is set, \
                 so the node will proceed on the un-verified executor. Its state transitions are NOT \
                 shadowed by the proved Lean kernel — do not present this node as verified."
            );
        } else {
            error!(
                "REFUSING TO START: `dregg_lean_ffi::lean_available()` is false — this binary was \
                 linked WITHOUT the verified Lean executor archive (libdregg_lean.a) and would run \
                 the UN-VERIFIED Rust executor. A node (solo OR full) MUST NOT serve as if verified \
                 while running the un-verified executor. Rebuild against a closure-complete, \
                 HEAD-matching Lean archive: `./scripts/bootstrap.sh` (and set DREGG_REQUIRE_LEAN=1 \
                 in CI/distribution builds so a marshal-only degrade fails the build instead of \
                 shipping silently — a --release build now defaults that gate ON). To deliberately \
                 run an un-verified node, set DREGG_ALLOW_UNVERIFIED_CONSENSUS=1. A stale or \
                 gitignored seed silently degrades to marshal-only — see \
                 docs/BUILD-LEAN-LINKED-NODE.md."
            );
            std::process::exit(1);
        }
    } else {
        info!(
            "verified-executor archive linked: `dregg_lean_ffi::lean_available()` is true — this \
             node runs the PROVED Lean executor over the C ABI"
        );
    }

    // ── VERIFIED-CONSENSUS STARTUP HARD-CHECK (red-team parity #6/#7) ──────────
    // A node in FULL (multi-party BFT) federation mode is a verified-consensus role:
    // it finalizes over `BlocklaceFinality.tauOrder`, the order the Lean-exported
    // `dregg_tau_order` computes. If the verified archive is NOT linked (a
    // marshal-only / stale build where `tau_order_available()` is false), the node
    // would SILENTLY degrade to the un-verified Rust `ordering::tau` per poll (a
    // `warn!` only — see `blocklace_sync`'s fallback). For a node that is SUPPOSED to
    // be Lean-shadowed that is fail-OPEN: it claims verified production+consensus
    // while running unverified ordering. Refuse to start instead (fail-CLOSED for
    // this role). A solo node (committee-of-one, trivial order) and a node that never
    // federates are unaffected, so the intentional mixed rust/lean network keeps
    // working — only the verified-role node refuses to run unverified.
    //
    // Escape hatch: `DREGG_ALLOW_UNVERIFIED_CONSENSUS=1` lets an operator who
    // deliberately accepts the un-verified Rust ordering proceed (e.g. a dev box with
    // a marshal-only archive). It is opt-IN — the default for a full-mode node is to
    // refuse.
    if !is_solo_mode && !dregg_lean_ffi::tau_order_available() {
        // Reuses the `allow_unverified` escape hatch parsed above (the same
        // DREGG_ALLOW_UNVERIFIED_CONSENSUS variable governs both gates).
        if allow_unverified {
            tracing::warn!(
                "VERIFIED-CONSENSUS HARD-CHECK OVERRIDDEN: this node is in FULL (multi-party BFT) \
                 mode but the Lean verified-consensus archive is NOT linked (`dregg_tau_order` \
                 absent). DREGG_ALLOW_UNVERIFIED_CONSENSUS is set, so the node will proceed on the \
                 UN-VERIFIED Rust `ordering::tau` — its finality is NOT shadowed by the verified \
                 rule. Do not use this in a federation that expects verified consensus."
            );
        } else {
            error!(
                "REFUSING TO START: this node is configured for VERIFIED consensus (federation \
                 mode FULL — multi-party BFT finality), but the Lean verified-consensus archive is \
                 not linked: `dregg_lean_ffi::tau_order_available()` is false (the build lacks the \
                 `dregg_tau_order` export, e.g. a marshal-only / stale archive). A verified-role \
                 node MUST NOT silently fall back to the un-verified Rust ordering. Rebuild the \
                 node against the closure-complete verified archive (it splices \
                 Dregg2.Distributed.FinalityGate), run this node in `--federation-mode solo` if it \
                 is not meant to finalize, or set DREGG_ALLOW_UNVERIFIED_CONSENSUS=1 to explicitly \
                 accept un-verified ordering."
            );
            std::process::exit(1);
        }
    } else if !is_solo_mode {
        info!(
            "verified-consensus hard-check passed: the Lean `dregg_tau_order` archive is linked — \
             this full-mode node finalizes over the VERIFIED ordering rule"
        );
    }

    // Phase C: Log multi-group participation if --groups is specified.
    // Actual group membership is resolved once the blocklace syncs and the
    // group registry is available. For now we validate the group IDs.
    if !groups.is_empty() {
        let mut valid_groups = 0usize;
        for group_hex in &groups {
            if group_hex.len() != 64 {
                error!(
                    group = %group_hex,
                    "invalid group ID (expected 64 hex chars), skipping"
                );
                continue;
            }
            if hex_decode_32(group_hex).is_some() {
                valid_groups += 1;
            } else {
                error!(
                    group = %group_hex,
                    "invalid hex for group ID, skipping"
                );
            }
        }
        if valid_groups > 0 {
            info!(
                group_count = valid_groups,
                "multi-group mode enabled (Phase C cross-reference dissemination)"
            );
        }
    }

    // Install Prometheus metrics recorder.
    let metrics_handle = metrics::install_recorder();

    info!(
        port = port,
        data_dir = %data_path.display(),
        pruning = enable_pruning,
        checkpoint_interval = checkpoint_interval,
        blocklace_checkpoint_interval,
        blocklace_wave_timeout_ms,
        faucet = enable_faucet,
        federation_mode = if is_solo_mode { "solo" } else { "full" },
        "starting dregg-node"
    );

    // F-CRIT-2: gate auto-approval of federation join proposals on CLI flag or
    // `.devnet` marker. Defaults to false otherwise — any peer publishing a
    // MembershipAction::Join used to be enough to flip the federation.
    let auto_approve_joins = auto_approve_joins_flag || data_path.join(".devnet").exists();
    if auto_approve_joins {
        tracing::warn!(
            "auto-approve-joins is ENABLED — any peer publishing a join proposal \
             will receive our approval vote. Disable in production."
        );
    }

    // Spawn federation sync background task based on the chosen consensus engine.
    //
    // The blocklace runs in EVERY configuration, including solo with no peers.
    // Solo is a committee-of-one: a real `Blocklace` (real Ed25519-signed blocks,
    // real blake3 block IDs, real parent links to prior tips, real tau ordering
    // which is trivial at n=1). This is the only way the node produces real
    // blocks with real parent hashes — the prior `solo_consensus` path only
    // bumped an in-memory height counter and produced no DAG at all.
    match consensus_engine {
        "blocklace" => {
            info!(
                consensus = "blocklace",
                solo = is_solo_mode,
                has_peers,
                "using blocklace (Cordial Miners) consensus"
            );
            let sync_state = node_state.clone();
            let gossip_port_copy = gossip_port;
            // Idle-heartbeat window: env var wins over the CLI flag so an
            // operator can retune a deployed unit via /etc/dregg/node.env
            // without editing the systemd ExecStart line (same pattern as
            // DREGG_PROVE_TURNS above).
            let idle_heartbeat_ms = std::env::var("DREGG_IDLE_HEARTBEAT_MS")
                .ok()
                .and_then(|v| v.trim().parse::<u64>().ok())
                .unwrap_or(idle_heartbeat_ms);
            // Min-block-interval rate cap: env var wins over the CLI flag, same
            // retune-a-deployed-unit pattern as DREGG_IDLE_HEARTBEAT_MS above.
            let min_block_interval_ms = std::env::var("DREGG_MIN_BLOCK_INTERVAL_MS")
                .ok()
                .and_then(|v| v.trim().parse::<u64>().ok())
                .unwrap_or(min_block_interval_ms);
            // SELF-FORMING MESH: derive our advertised gossip endpoint from the
            // operator-configured `--bind <ip>` and the gossip port. Only a
            // concrete, routable IP is advertised — an unspecified bind (0.0.0.0/
            // ::) is not dialable, so self-advertisement stays off there and the
            // node falls back to manual `--federation-peers`.
            let advertise_addr: Option<SocketAddr> = bind
                .parse::<std::net::IpAddr>()
                .ok()
                .filter(|ip| !ip.is_unspecified())
                .map(|ip| SocketAddr::new(ip, gossip_port_copy));
            let blocklace_handle = blocklace_sync::run_blocklace_sync(
                sync_state,
                gossip_port_copy,
                auto_approve_joins,
                blocklace_checkpoint_interval,
                blocklace_wave_timeout_ms,
                block_cadence_ms,
                idle_heartbeat_ms,
                min_block_interval_ms,
                advertise_addr,
            )
            .await;
            if let Some(handle) = blocklace_handle {
                node_state.set_blocklace(handle).await;
            }
        }
        _ => {
            error!(
                consensus = %consensus_engine,
                "unknown consensus engine"
            );
            std::process::exit(1);
        }
    }

    // Assemble the CORS allowlist: union of --cors-origin flags and the
    // DREGG_CORS_ORIGINS env var (comma-separated). Empty by default →
    // locked down to localhost + browser extensions.
    let mut cors_origins: std::collections::HashSet<String> =
        cors_origins_flag.into_iter().collect();
    if let Ok(env_origins) = std::env::var("DREGG_CORS_ORIGINS") {
        for o in env_origins.split(',') {
            let o = o.trim();
            if !o.is_empty() {
                cors_origins.insert(o.to_string());
            }
        }
    }
    if !cors_origins.is_empty() {
        let mut sorted: Vec<&String> = cors_origins.iter().collect();
        sorted.sort();
        info!(origins = ?sorted, "CORS: allowing extra cross-origin origins (plus localhost/extensions)");
    }

    // Build and serve the HTTP API.
    let app = api::router_with_cors(
        node_state.clone(),
        enable_faucet,
        metrics_handle,
        cors_origins,
    )
    .into_make_service_with_connect_info::<SocketAddr>();
    let bind_addr: std::net::IpAddr = bind.parse().unwrap_or_else(|_| {
        error!("invalid --bind address: {bind}, falling back to 127.0.0.1");
        Ipv4Addr::LOCALHOST.into()
    });
    let addr = SocketAddr::new(bind_addr, port);

    if bind_addr == std::net::IpAddr::V4(Ipv4Addr::UNSPECIFIED)
        || bind_addr == std::net::IpAddr::V6(std::net::Ipv6Addr::UNSPECIFIED)
    {
        tracing::warn!(
            %addr,
            "binding to all interfaces — faucet, cipherclerk, bridge endpoints are exposed to the network"
        );
    }

    info!(%addr, "HTTP API listening");

    let listener = tokio::net::TcpListener::bind(addr)
        .await
        .expect("failed to bind HTTP listener");

    // pg-dregg §11.4 (M3): spawn the submit-queue drainer — the READ side of the
    // write loop, symmetric to the pg_mirror WRITE side. OFF by default; it
    // connects ONLY when the `pg-mirror-live` feature is built AND
    // DREGG_PG_MIRROR_URL is set (returns None otherwise, so node behaviour is
    // byte-identical when unset). It tails dregg.submit_queue, runs each queued
    // signed turn through the real verified executor, and walks the row's status
    // pending → executed | refused. Shares the same NodeState handle as the HTTP
    // server (like the prove pool); the task ends when the runtime shuts down.
    #[cfg(feature = "pg-mirror-live")]
    let _submit_drainer = submit_queue_drainer::spawn(node_state.clone());

    // THE DEOS-HOST: if `--deos-program` was given, host a headless userspace deos-js
    // private server. On boot the node mints the server cell, runs the program's setup
    // (registering cap-gated affordances via `deos.server.*`), and publishes its
    // affordance surface for client discovery — the node as a headless deos-js-server-host.
    #[cfg(feature = "deos-host")]
    if let Some(ref program_path) = deos_program {
        match std::fs::read_to_string(program_path) {
            Ok(program) => match deos_host::host_server_program(
                &node_state,
                "deos-server",
                dregg_cell::AuthRequired::None,
                program,
            )
            .await
            {
                Ok(server_cell) => info!(
                    server_cell = %dregg_types::hex_encode(server_cell.as_bytes()),
                    program = %program_path,
                    "DEOS-HOST: hosting a userspace private server; affordances discoverable at \
                     GET /api/server/{}/affordances",
                    dregg_types::hex_encode(server_cell.as_bytes())
                ),
                Err(e) => {
                    error!(error = %e, program = %program_path, "DEOS-HOST: failed to host program")
                }
            },
            Err(e) => {
                error!(error = %e, program = %program_path, "DEOS-HOST: cannot read program file")
            }
        }
    }
    #[cfg(not(feature = "deos-host"))]
    if deos_program.is_some() {
        tracing::warn!(
            "--deos-program given but the `deos-host` feature is OFF; the flag is inert. \
             Rebuild with `--features deos-host` to host a userspace deos-js private server."
        );
    }

    // P2 Fix 8: Graceful shutdown on Ctrl-C.
    axum::serve(listener, app)
        .with_graceful_shutdown(shutdown_signal())
        .await
        .expect("HTTP server error");

    // Persist critical state before exiting.
    node_state.persist_on_shutdown().await;

    info!("HTTP server shut down gracefully");
}

/// Initialize the data directory: create it and generate a keypair.
fn init_node(data_dir: &str) {
    let data_path = expand_path(data_dir);

    if data_path.exists() {
        println!("Data directory already exists: {}", data_path.display());
        println!("Skipping initialization.");
        return;
    }

    std::fs::create_dir_all(&data_path).expect("failed to create data directory");

    // Generate a node keypair and store the public key for display.
    let mut key_bytes = [0u8; 32];
    getrandom::fill(&mut key_bytes).expect("getrandom failed");

    // Write the secret key to the data dir (in production, use a keyring).
    let key_path = data_path.join("node.key");
    std::fs::write(&key_path, key_bytes).expect("failed to write node key");

    // Restrict file permissions to owner read/write only (0600).
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&key_path, std::fs::Permissions::from_mode(0o600))
            .expect("failed to set node.key permissions");
    }

    // Derive public key for display.
    let signing_key = ed25519_dalek::SigningKey::from_bytes(&key_bytes);
    let public_key = signing_key.verifying_key();
    let pk_hex: String = public_key
        .to_bytes()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();

    println!(
        "Initialized dregg-node data directory: {}",
        data_path.display()
    );
    println!("Node public key: {pk_hex}");
    println!();
    println!("Start the node with:");
    println!("  dregg-node run --data-dir {}", data_dir);
}

/// Check if the node is reachable on its HTTP port.
///
/// Uses a raw TCP connect (no extra HTTP client dep in the node binary).
/// This is a basic liveness check only; a full semantic probe of /status
/// would require an HTTP client. On success we still recommend hitting the
/// URL to confirm it's a real dregg-node (not another service on the port).
async fn check_status(port: u16) {
    let url = format!("http://127.0.0.1:{port}/status");

    // Use a raw TCP connection to check — avoids adding reqwest as a dep.
    let addr = SocketAddr::new(Ipv4Addr::LOCALHOST.into(), port);
    match tokio::net::TcpStream::connect(addr).await {
        Ok(_) => {
            println!("dregg-node port {port} is accepting TCP connections.");
            println!("  Try the status endpoint for full details: {url}");
            println!(
                "  (If another service is bound there, the HTTP response will not be dregg's.)"
            );
        }
        Err(_) => {
            println!("dregg-node is NOT listening on port {port}");
            std::process::exit(1);
        }
    }
}

/// Expand `~` in a path string.
fn expand_path(path: &str) -> PathBuf {
    if path.starts_with("~/")
        && let Some(home) = dirs_home()
    {
        return home.join(&path[2..]);
    }
    PathBuf::from(path)
}

/// Get the home directory.
fn dirs_home() -> Option<PathBuf> {
    std::env::var_os("HOME").map(PathBuf::from)
}

/// Run the MCP server: initialize node state and serve over stdio.
async fn run_mcp(data_dir: &str, peers: Vec<String>) {
    let data_path = expand_path(data_dir);

    if !data_path.exists() {
        error!(
            "data directory does not exist: {}. Run `dregg-node init` first.",
            data_path.display()
        );
        std::process::exit(1);
    }

    let node_state = match state::NodeState::new(&data_path, peers) {
        Ok(s) => s,
        Err(e) => {
            error!("failed to initialize node state: {e}");
            std::process::exit(1);
        }
    };

    // F-DOS-1: async prove pool here too, so the MCP tool commit paths offload
    // proving off the write lock rather than blocking inline.
    {
        let pool = prove_pool::ProvePool::spawn(node_state.clone());
        node_state.set_prove_pool(pool).await;
    }

    // MCP stdio mode runs as a single-user CLI — no remote attacker scenario
    // applies. Start the cipherclerk unlocked so the tools can proceed without an
    // explicit unlock step. (HTTP mode keeps the passphrase requirement.)
    {
        let mut s = node_state.write().await;
        s.unlocked = true;
    }

    mcp::run_stdio(node_state).await;
}

/// Run the relay operator service.
#[allow(clippy::too_many_arguments)]
async fn run_relay(
    port: u16,
    bond: u64,
    max_capacity: usize,
    gc_interval: u64,
    message_ttl: u64,
    max_delivery_latency: u64,
    state_file: PathBuf,
    data_dir: &str,
    default_inbox_capacity: usize,
    default_min_deposit: u64,
    min_message_deposit: u64,
    subscription_fee: u64,
) {
    let data_path = expand_path(data_dir);

    // Read operator key from the data directory.
    let operator_key = if data_path.join("node.key").exists() {
        let key_bytes = std::fs::read(data_path.join("node.key"))
            .expect("failed to read node.key for relay operator identity");
        let mut key = [0u8; 32];
        key.copy_from_slice(&key_bytes[..32]);
        key
    } else {
        error!(
            "no node.key found in {}. Run `dregg-node init` first.",
            data_path.display()
        );
        std::process::exit(1);
    };

    let config = relay_service::RelayConfig {
        listen_port: port,
        operator_key,
        bond_amount: bond,
        fee_policy: relay_service::FeePolicy {
            min_deposit_computrons: min_message_deposit,
            subscription_fee,
            accept_external_assets: false,
            external_rate_micros: 1_000_000,
        },
        max_total_capacity: max_capacity,
        gc_interval_secs: gc_interval,
        message_ttl_blocks: message_ttl,
        max_delivery_latency_blocks: max_delivery_latency,
        state_file,
        default_inbox_capacity,
        default_min_deposit,
    };

    relay_service::run_relay_service(config).await;
}

/// Decode a 64-char hex string into a [u8; 32].
fn hex_decode_32(s: &str) -> Option<[u8; 32]> {
    if s.len() != 64 {
        return None;
    }
    let mut bytes = [0u8; 32];
    for (i, byte) in bytes.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).ok()?;
    }
    Some(bytes)
}

#[derive(Default)]
struct GenesisCellLoadStats {
    inserted: usize,
    existing: usize,
    skipped: usize,
    invalid: usize,
}

impl GenesisCellLoadStats {
    fn total(&self) -> usize {
        self.inserted + self.existing + self.skipped + self.invalid
    }
}

/// Materialize supported genesis `initial_cells` entries into the in-memory ledger.
///
/// The current cell model can create canonical hosted cells when genesis provides
/// a public key, token id, and balance. Label-only entries are skipped because
/// turning an arbitrary label into a signing public key would create cells that
/// no holder can authorize.
///
/// THE EPOCH §5 ("genesis as issuer-moves"): when the genesis carries
/// `genesis_moves`, every cell is inserted at ZERO balance (value-empty
/// genesis) and value enters ONLY by replaying the issuer-moves — the well
/// is well-debited (goes negative, −supply) and each recipient credited —
/// after which every declared `balance` is verified against the outcome.
/// The deployed chain therefore starts inside guarantee B's hypotheses
/// (`reachable_total_zero`). A genesis without `genesis_moves` (legacy)
/// materializes declared balances directly.
fn materialize_genesis_cells(
    genesis: &serde_json::Value,
    ledger: &mut dregg_cell::Ledger,
) -> GenesisCellLoadStats {
    let mut stats = GenesisCellLoadStats::default();
    let Some(initial_cells) = genesis["initial_cells"].as_array() else {
        return stats;
    };
    let moves = genesis["genesis_moves"].as_array();
    let seed_by_moves = moves.is_some_and(|m| !m.is_empty());

    // Declared (post-seed) balances by cell id, for the issuer-move
    // verification pass.
    let mut declared: Vec<(dregg_cell::CellId, i64)> = Vec::new();

    for cell in initial_cells {
        let label = cell["id"]
            .as_str()
            .or_else(|| cell["name"].as_str())
            .unwrap_or("<unnamed>");

        // SIGNED balance (THE EPOCH §5): the issuer well declares a negative
        // post-seed balance.
        let Some(balance) = cell["balance"].as_i64() else {
            tracing::warn!(cell = %label, "skipping genesis cell without i64 balance");
            stats.invalid += 1;
            continue;
        };
        if !seed_by_moves && balance < 0 {
            tracing::warn!(
                cell = %label,
                "skipping negative-balance genesis cell without genesis_moves (a well needs issuer-moves to be derived)"
            );
            stats.invalid += 1;
            continue;
        }

        let Some(public_key_hex) = cell["public_key"].as_str() else {
            tracing::warn!(
                cell = %label,
                "skipping genesis cell without public_key; current ledger needs a public key to materialize a canonical cell",
            );
            stats.skipped += 1;
            continue;
        };
        let Some(public_key) = hex_decode_32(public_key_hex) else {
            tracing::warn!(cell = %label, "skipping genesis cell with malformed public_key");
            stats.invalid += 1;
            continue;
        };

        let token_id = match cell["token_id"].as_str() {
            Some(token_id_hex) => match hex_decode_32(token_id_hex) {
                Some(token_id) => token_id,
                None => {
                    tracing::warn!(cell = %label, "skipping genesis cell with malformed token_id");
                    stats.invalid += 1;
                    continue;
                }
            },
            None => [0u8; 32],
        };

        // Issuer-move seeding inserts the cell VALUE-EMPTY; legacy seeding
        // installs the declared balance directly.
        let initial_balance = if seed_by_moves { 0 } else { balance };
        let ledger_cell = dregg_cell::Cell::with_balance(public_key, token_id, initial_balance);
        let cell_id = ledger_cell.id();
        if let Some(declared_id_hex) = cell["id"].as_str().filter(|id| id.len() == 64) {
            match hex_decode_32(declared_id_hex) {
                Some(declared_id) if dregg_cell::CellId(declared_id) == cell_id => {}
                Some(_) => {
                    tracing::warn!(
                        cell = %label,
                        derived = %dregg_types::hex_encode(&cell_id.0),
                        "skipping genesis cell whose declared id does not match public_key/token_id",
                    );
                    stats.invalid += 1;
                    continue;
                }
                None => {
                    tracing::warn!(cell = %label, "skipping genesis cell with malformed hex id");
                    stats.invalid += 1;
                    continue;
                }
            }
        }

        if ledger.get(&cell_id).is_some() {
            stats.existing += 1;
            continue;
        }

        match ledger.insert_cell(ledger_cell) {
            Ok(_) => {
                stats.inserted += 1;
                declared.push((cell_id, balance));
            }
            Err(dregg_cell::LedgerError::CellAlreadyExists(_)) => stats.existing += 1,
            Err(e) => {
                tracing::warn!(cell = %label, error = %e, "failed to insert genesis cell");
                stats.invalid += 1;
            }
        }
    }

    // THE EPOCH §5: replay the issuer-moves over the value-empty cells. Each
    // move WELL-debits the source (may go negative — the issuer well carries
    // −supply) and credits the recipient.
    if seed_by_moves {
        for mv in moves.into_iter().flatten() {
            let (Some(from_hex), Some(to_hex), Some(amount)) = (
                mv["from"].as_str(),
                mv["to"].as_str(),
                mv["amount"].as_u64(),
            ) else {
                tracing::warn!("skipping malformed genesis_moves entry: {mv}");
                continue;
            };
            let (Some(from_id), Some(to_id)) = (hex_decode_32(from_hex), hex_decode_32(to_hex))
            else {
                tracing::warn!("skipping genesis move with malformed cell ids");
                continue;
            };
            let from_id = dregg_cell::CellId(from_id);
            let to_id = dregg_cell::CellId(to_id);
            let Some(from_cell) = ledger.get_mut(&from_id) else {
                tracing::warn!(from = %from_hex, "genesis move source not in ledger; skipping");
                continue;
            };
            if !from_cell.state.well_debit_balance(amount) {
                tracing::warn!(from = %from_hex, amount, "genesis well debit overflow; skipping");
                continue;
            }
            let Some(to_cell) = ledger.get_mut(&to_id) else {
                // Restore the debit so the books stay closed.
                if let Some(from_cell) = ledger.get_mut(&from_id) {
                    let _ = from_cell.state.credit_balance(amount);
                }
                tracing::warn!(to = %to_hex, "genesis move recipient not in ledger; skipping");
                continue;
            };
            if !to_cell.state.credit_balance(amount) {
                if let Some(from_cell) = ledger.get_mut(&from_id) {
                    let _ = from_cell.state.credit_balance(amount);
                }
                tracing::warn!(to = %to_hex, amount, "genesis credit overflow; skipping");
            }
        }

        // Verify the declared post-seed balances (and, transitively, that
        // the value column sums to zero exactly when the declarations do).
        for (cell_id, expect) in &declared {
            let got = ledger.get(cell_id).map(|c| c.state.balance());
            if got != Some(*expect) {
                tracing::error!(
                    cell = %dregg_types::hex_encode(&cell_id.0),
                    expected = expect,
                    got = ?got,
                    "genesis issuer-move outcome does not match the declared balance"
                );
                stats.invalid += 1;
            }
        }
    }

    stats
}

/// Reconstruct the recovered ledger in the SOUND order — genesis BASELINE
/// first, commit-log overlay SECOND — returning the genesis materialization
/// stats.
///
/// On entry `ledger` holds the recovered commit-log overlay that
/// `NodeState::new_with_key_file` left in place: `checkpoint ⊕ touched
/// post-states`. The genesis baseline is the height-0 truth that belongs
/// UNDER that overlay; the overlay is the later finalized truth that belongs
/// ON it. So this:
///
///   1. lifts the recovered overlay out of the live ledger,
///   2. materializes the genesis baseline on a FRESH ledger, so the
///      `genesis_moves` replay EXACTLY ONCE over value-empty cells (the issuer
///      well goes −supply; each recipient is credited once),
///   3. re-applies the overlay LAST-WRITER-WINS (remove-then-insert, the
///      verified `CrashRecovery.upd` point update) so every bot-touched cell's
///      FINALIZED post-state OVERWRITES its genesis-baseline value.
///
/// The result is `genesis_baseline ⊕ overlay` exactly — the state the recorded
/// finalized root commits.
///
/// This replaces the old order (genesis reseed applied OVER the overlay), which
/// replayed the `genesis_moves` across the WHOLE ledger and so re-credited
/// every move RECIPIENT already present in the overlay — a double-credit (e.g.
/// the faucet cell, already carrying its post-bot value) that made the
/// reconstructed root diverge from the recorded finalized root and fail-closed
/// a healthy node. An issuer-well genesis (issuer cell funding recipients via
/// `genesis_moves`) surfaces this; a move-free genesis never did. Reordering
/// does NOT loosen the integrity verdict: a genuinely divergent overlay STILL
/// reconstructs a wrong root, and `verify_recovery_convergence` STILL refuses
/// to start (STORE INTEGRITY EVENT).
fn reseed_genesis_then_overlay(
    genesis: &serde_json::Value,
    ledger: &mut dregg_cell::Ledger,
) -> GenesisCellLoadStats {
    // 1. Lift the recovered commit-log overlay (checkpoint ⊕ touched
    //    post-states) out of the live ledger.
    let recovered_overlay: Vec<dregg_cell::Cell> = ledger.iter().map(|(_, c)| c.clone()).collect();
    *ledger = dregg_cell::Ledger::new();

    // 2. Genesis baseline on a FRESH ledger: genesis_moves apply EXACTLY ONCE
    //    over value-empty cells.
    let stats = materialize_genesis_cells(genesis, ledger);

    // 3. Re-apply the overlay LAST-WRITER-WINS so every bot-touched cell's
    //    finalized post-state OVERWRITES its genesis-baseline value.
    for cell in recovered_overlay {
        let _ = ledger.remove(&cell.id());
        let _ = ledger.insert_cell(cell);
    }

    stats
}

/// Register a peer federation in this node's `known_federations/`
/// directory. Reads the descriptor JSON, sanity-checks that
/// `federation_id == H(sorted_committee_pubkeys || committee_epoch)`,
/// and writes the descriptor verbatim to
/// `<data-dir>/known_federations/<federation_id>.json` so the running
/// node can pick it up.
///
/// This is the out-of-band cross-federation trust setup step from
/// `SILVER-VISION-E2E-VERIFICATION.md` §0.2 / §4.2. Production deployments
/// will replace this with a more sophisticated "federation discovery"
/// flow (out of scope for Silver).
fn run_register_federation(data_dir: &str, descriptor: &std::path::Path) {
    let data_path = expand_path(data_dir);
    if !data_path.exists() {
        eprintln!(
            "error: data directory does not exist: {}. Run `dregg-node init` first.",
            data_path.display()
        );
        std::process::exit(1);
    }

    let text = match std::fs::read_to_string(descriptor) {
        Ok(t) => t,
        Err(e) => {
            eprintln!(
                "error: cannot read descriptor {}: {e}",
                descriptor.display()
            );
            std::process::exit(1);
        }
    };
    let parsed: serde_json::Value = match serde_json::from_str(&text) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("error: cannot parse descriptor JSON: {e}");
            std::process::exit(1);
        }
    };

    // Extract federation_id and validators.
    let declared_fed_id = parsed["federation_id"].as_str().unwrap_or("").to_string();
    if declared_fed_id.len() != 64 {
        eprintln!(
            "error: descriptor missing or malformed `federation_id` (got: {declared_fed_id:?}); expected 64-char hex",
        );
        std::process::exit(1);
    }
    let committee_epoch = parsed["committee_epoch"].as_u64().unwrap_or(0);

    let validators = match parsed["validators"].as_array() {
        Some(v) => v,
        None => {
            eprintln!("error: descriptor missing `validators` array");
            std::process::exit(1);
        }
    };
    let mut pubkeys: Vec<dregg_types::PublicKey> = Vec::with_capacity(validators.len());
    for v in validators {
        let pk_hex = match v["public_key"].as_str() {
            Some(s) => s,
            None => {
                eprintln!("error: validator entry missing `public_key`");
                std::process::exit(1);
            }
        };
        let bytes = match hex_decode_32(pk_hex) {
            Some(b) => b,
            None => {
                eprintln!("error: validator public_key is not 64-char hex: {pk_hex:?}");
                std::process::exit(1);
            }
        };
        pubkeys.push(dregg_types::PublicKey(bytes));
    }
    if pubkeys.is_empty() {
        eprintln!("error: descriptor has zero validators");
        std::process::exit(1);
    }

    // Recompute the federation_id and reject a tampered descriptor.
    let derived = dregg_federation::derive_federation_id_with_epoch(&pubkeys, committee_epoch);
    let derived_hex: String = derived.iter().map(|b| format!("{b:02x}")).collect();
    if derived_hex != declared_fed_id {
        eprintln!(
            "error: descriptor federation_id ({}) does not match committee-derived id ({}). \
             Refusing to register a tampered descriptor (audit F1).",
            declared_fed_id, derived_hex
        );
        std::process::exit(1);
    }

    // Write into `<data-dir>/known_federations/<federation_id>.json`.
    let registry_dir = data_path.join("known_federations");
    if let Err(e) = std::fs::create_dir_all(&registry_dir) {
        eprintln!("error: cannot create {}: {e}", registry_dir.display());
        std::process::exit(1);
    }
    let out_path = registry_dir.join(format!("{declared_fed_id}.json"));
    if let Err(e) = std::fs::write(&out_path, &text) {
        eprintln!("error: cannot write {}: {e}", out_path.display());
        std::process::exit(1);
    }

    println!(
        "Registered federation {} (epoch={}, n_validators={}) in {}",
        declared_fed_id,
        committee_epoch,
        pubkeys.len(),
        out_path.display()
    );
}

/// Decide whether a node configured `--federation-mode solo` should AUTO-UPGRADE
/// to full (BFT-quorum) mode because peers are present. Peer-presence drives the
/// mode: a configured peer list (`has_peers`) and/or a multi-member genesis
/// committee (`committee_size > 1`) means the node is meant to federate, not sit
/// silently solo. Returns true only when the node is currently solo AND peers are
/// present. A genuine solo node (no peers, committee of one) is left untouched.
fn solo_should_auto_upgrade(is_solo_mode: bool, has_peers: bool, committee_size: usize) -> bool {
    is_solo_mode && (has_peers || committee_size > 1)
}

/// Parse the `DREGG_ALLOW_UNVERIFIED_CONSENSUS` escape hatch (shared by the
/// marshal-only startup tripwire and the verified-consensus hard-check). Running an
/// un-verified executor / ordering is a DELIBERATE opt-in — this returns `true` only
/// when the operator explicitly set the variable to a truthy value.
fn env_allow_unverified(val: Option<&str>) -> bool {
    matches!(
        val,
        Some("1") | Some("true") | Some("TRUE") | Some("on") | Some("ON")
    )
}

/// Whether a node must REFUSE to start because it would run the UN-verified Rust
/// executor (`lean_available()==false`) without the explicit operator opt-in. Any
/// node — solo OR full — refuses unless the escape hatch is set, so an unverified
/// node is never a silent default.
fn marshal_only_must_refuse(lean_available: bool, allow_unverified: bool) -> bool {
    !lean_available && !allow_unverified
}

/// Wait for a shutdown signal to trigger a graceful, checkpoint-then-exit stop.
///
/// Handles BOTH SIGINT (Ctrl-C) and SIGTERM. `docker stop` (and systemd) send
/// SIGTERM, then SIGKILL after a grace period; the previous handler only caught
/// SIGINT, so `docker stop` mid-checkpoint killed the process before
/// `persist_on_shutdown` flushed a ledger checkpoint — leaving a sub-checkpoint
/// divergence that surfaced as a STORE INTEGRITY EVENT on restart. Catching
/// SIGTERM lets the normal stop path flush a checkpoint cleanly (the caller runs
/// `persist_on_shutdown` after this returns), removing the cause for graceful
/// stops. (The recovery side — a real crash / SIGKILL — is handled separately by
/// the crash-consistent identity-cursor resume.)
async fn shutdown_signal() {
    #[cfg(unix)]
    {
        use tokio::signal::unix::{SignalKind, signal};
        let mut sigterm =
            signal(SignalKind::terminate()).expect("failed to install SIGTERM handler");
        tokio::select! {
            _ = tokio::signal::ctrl_c() => {
                info!("received SIGINT (Ctrl-C), initiating graceful checkpoint-then-exit shutdown");
            }
            _ = sigterm.recv() => {
                info!(
                    "received SIGTERM (docker stop / systemd), initiating graceful \
                     checkpoint-then-exit shutdown"
                );
            }
        }
    }
    #[cfg(not(unix))]
    {
        tokio::signal::ctrl_c()
            .await
            .expect("failed to listen for Ctrl-C");
        info!("received Ctrl-C, initiating graceful checkpoint-then-exit shutdown");
    }
}

#[cfg(test)]
mod shutdown_and_federation_tests {
    use super::*;

    // ── BUG 2: federation auto-upgrade out of solo when peers are present ──────

    #[test]
    fn genuine_solo_node_is_not_upgraded() {
        // No peer list, committee of one (or none) ⇒ a real solo node, untouched.
        assert!(!solo_should_auto_upgrade(true, false, 0));
        assert!(!solo_should_auto_upgrade(true, false, 1));
    }

    #[test]
    fn solo_with_peer_list_upgrades() {
        // Configured solo but a peer list is present ⇒ upgrade.
        assert!(solo_should_auto_upgrade(true, true, 0));
        assert!(solo_should_auto_upgrade(true, true, 1));
    }

    #[test]
    fn solo_with_multi_member_committee_upgrades() {
        // Configured solo but a multi-member genesis committee ⇒ upgrade even
        // with no explicit peer list.
        assert!(solo_should_auto_upgrade(true, false, 3));
    }

    #[test]
    fn full_mode_is_never_force_downgraded_or_re_flagged() {
        // A node already in full mode is never the subject of this upgrade
        // (the helper only fires when currently solo).
        assert!(!solo_should_auto_upgrade(false, true, 5));
        assert!(!solo_should_auto_upgrade(false, false, 1));
    }

    // ── MARSHAL-ONLY startup refusal (fail-closed unless explicit opt-in) ──────

    #[test]
    fn env_allow_unverified_only_on_explicit_truthy() {
        for v in ["1", "true", "TRUE", "on", "ON"] {
            assert!(env_allow_unverified(Some(v)), "expected {v:?} to allow");
        }
        for v in ["0", "false", "off", "no", "", "yes", "2"] {
            assert!(!env_allow_unverified(Some(v)), "expected {v:?} to refuse");
        }
        // Unset (the default) never allows an un-verified executor.
        assert!(!env_allow_unverified(None));
    }

    #[test]
    fn marshal_only_refuses_unless_escape_set() {
        // A verified build (lean linked) never refuses, regardless of the escape.
        assert!(!marshal_only_must_refuse(true, false));
        assert!(!marshal_only_must_refuse(true, true));
        // A marshal-only build REFUSES by default (no silent unverified default)…
        assert!(marshal_only_must_refuse(false, false));
        // …and only proceeds when the operator explicitly opts in.
        assert!(!marshal_only_must_refuse(false, true));
    }

    // ── BUG 4: graceful shutdown wires SIGTERM (docker stop) ───────────────────
    //
    // The cause of the restart STORE INTEGRITY EVENT was that `docker stop`
    // sends SIGTERM, which the old handler (SIGINT-only) ignored — the process
    // was SIGKILLed before `persist_on_shutdown` flushed a checkpoint. The fix
    // makes `shutdown_signal` select on a SIGTERM stream too. This test asserts
    // the exact platform mechanism the fix relies on installs cleanly (a genuine
    // raise-and-deliver test is avoided here because signal disposition is
    // process-global and would be flaky under the parallel test harness).
    #[cfg(unix)]
    #[tokio::test]
    async fn sigterm_stream_installs() {
        use tokio::signal::unix::{SignalKind, signal};
        let s = signal(SignalKind::terminate());
        assert!(
            s.is_ok(),
            "graceful shutdown requires a SIGTERM (terminate) stream to install on unix so \
             `docker stop` checkpoints-then-exits instead of being SIGKILLed mid-checkpoint"
        );
    }
}
