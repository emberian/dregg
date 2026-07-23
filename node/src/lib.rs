//! `dregg-node`: The federation node daemon library.
//!
//! This crate is the reusable library behind the `dregg-node` binary. It hosts:
//! - An AgentCipherclerk with token management
//! - Participation in federation consensus (attested roots)
//! - A localhost HTTP API for the browser extension cipherclerk
//! - State sync with federation peers
//!
//! The thin `src/main.rs` bin parses the CLI and dispatches to [`run`]; every
//! module below is the library's public surface (which is why they carry no
//! `#[allow(dead_code)]` on their public API — they are legitimately public).

pub mod api;
pub mod blocklace_sync;
pub mod catchup;
pub mod channels_service;
pub mod committee_replay;
pub mod config;
pub mod coord_gate;
/// THE ENCRYPTED CALL AUCTION on the node's own surface: trader-encrypted, signed BFV order
/// ingress, a carry-free homomorphic fold, a masked quorum boundary, an MPC crossing that reveals
/// only `(p*, V*)`, and a quorum-co-signed attested clearing receipt. Gated to the Lean-emitted
/// `dark-bazaar-private-n4k4` family; fails closed on committee / verified-core / certificate.
pub mod dark_clearing_service;
// THE DEOS-HOST (opt-in `deos-host` feature): the node hosts a headless userspace
// deos-js "private server" program. Pulls in mozjs via deos-js, so it is feature-gated.
#[cfg(feature = "deos-host")]
pub mod deos_host;
#[cfg(all(test, feature = "deos-host"))]
mod deos_host_e2e;
#[cfg(all(test, feature = "deos-host"))]
mod deos_host_fork_client_e2e;
pub mod dkg_service;
pub mod finality_gate;
#[cfg(all(test, feature = "deos-host"))]
mod mud_e2e;
// THE PLAYABLE MUD CLIENT (`dregg-node mud-client`, `deos-host` feature): boots an
// in-process node, hosts the GM (`mud_play_gm.js`), and drops you into a text-MUD REPL
// that drives the living world with real verified turns over the node's HTTP wire.
#[cfg(feature = "deos-host")]
pub mod mud_client;
#[cfg(all(test, feature = "deos-host"))]
mod mud_client_e2e;
// THE LIVE SHARED WORLD (`deos-host` feature): two distinct identities co-inhabit ONE
// hosted world, each seeing the other's turns LIVE via the node's receipt event stream —
// the first real rung of MULTI-PERSON deos. Headless engine + its co-acting e2e proof.
#[cfg(test)]
mod captp_handoff_e2e;
#[cfg(test)]
mod epoch_transition_e2e;
pub mod equivocation_court_service;
pub mod events;
// The exact-FNSP-v3 cluster. These four carried `#[cfg(feature = "prover")]` until 2026-07-28,
// which never subtracted anything: `blocklace_sync.rs` names all four unconditionally at ~20 call
// sites, so the OFF position did not compile and no build ever ran without them.
mod exact_fnsp_v3_activation;
mod exact_fnsp_v3_actor_authority;
mod exact_fnsp_v3_execution_authority;
mod exact_fnsp_v3_finalization;
pub mod execution_cursor;
pub mod executor_setup;
mod executor_side_state_persistence;
mod executor_state_admission;
pub mod finalization_votes;
// DOES THE FAUCET MOVE THE MONEY? The e2e that asserts on the authoritative
// ledger after finalization, not on the HTTP response (which is staging only).
#[cfg(test)]
mod faucet_grant_e2e;
// CAN THE RECIPIENT SPEND IT? The other half of onboarding: faucet → the fresh
// client's OWN first turn → finalized, asserted on the authoritative ledger.
#[cfg(test)]
mod first_turn_e2e;
pub mod genesis;
pub mod gossip;
pub mod identity_export;
// `dregg-node init` — mints the one-validator chain `run` refuses to start
// without, through the same `genesis::run_genesis` the documented command uses.
mod init;
// CAN THE OPERATOR ACT AFTER SOMEBODY ELSE ACTED? The thin ingress stamped the
// node-WIDE receipt-log head as the agent's predecessor, so the faucet grant one
// step earlier made the next operator turn unsubmittable.
#[cfg(test)]
mod mailbox_crank_e2e;
pub mod mcp;
pub mod metrics;
#[cfg(test)]
mod node_integrator_e2e;
#[cfg(test)]
mod operator_turn_receipt_head_e2e;
// The operator onboarding dance (gen-validator-key / join / add-validator) — the
// slick, reusable path for folding a node + validator into a federation.
#[cfg(test)]
mod market_loop;
pub mod operator_join;
pub mod pg_mirror;
pub mod private_dependent_turns;
mod program_registry_persistence;
pub mod promise_resolutions;
pub mod prove_pool;
pub mod realm_service;
pub mod relay_dispute;
pub mod relay_service;
pub mod relay_slash_intake;
pub mod relay_slash_submit;
pub mod routing_table;
pub mod self_cell;
#[cfg(feature = "deos-host")]
pub mod shared_world;
#[cfg(all(test, feature = "deos-host"))]
mod shared_world_e2e;
pub mod signed_turn_validation;
pub mod slash_treasury_mirror;
pub mod starbridge_seed;
pub mod state;
pub mod storage_service;
pub mod strand_admission_gate;
#[cfg(feature = "pg-mirror-live")]
pub mod submit_queue_drainer;
pub mod trustline_service;
pub mod turn_proving;
pub mod ws;

use std::net::{Ipv4Addr, SocketAddr};
use std::path::PathBuf;

use clap::{Parser, Subcommand};
use tracing::{error, info, warn};

/// The `dregg-node` command-line interface.
#[derive(Parser)]
#[command(name = "dregg-node", about = "Dragon's Egg federation node daemon")]
pub struct Cli {
    #[command(subcommand)]
    pub command: Command,
}

/// The `dregg-node` subcommands.
#[derive(Subcommand)]
pub enum Command {
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

        /// DEVNET BRING-UP (loopback-only, explicit opt-in): start the cipherclerk
        /// UNLOCKED with NO passphrase so a local devnet demo anchors turns
        /// out-of-the-box — no manual `/cipherclerk/unlock` + bearer dance (that
        /// dance is what made every `/descent/submit` anchor soft-fail 403). This
        /// EXTENDS the MCP-stdio auto-unlock precedent (single-user, no remote
        /// attacker) to an EXPLICIT, loopback-gated HTTP mode. It is honored ONLY
        /// when BOTH hold: the node binds a loopback address (127.0.0.1 / ::1) AND
        /// no passphrase is already set for the data dir. On a network bind
        /// (`--bind 0.0.0.0`) or an already-passphrased data dir it is REFUSED (the
        /// node stays locked and logs why), so a production node is NEVER weakened.
        /// Also settable via `DREGG_DEV_UNLOCK=1`.
        #[arg(long = "dev-unlock")]
        dev_unlock: bool,
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

        /// Optional deployment domain used to derive deployment-local issuer /
        /// fee-well identities.  This does not replace the committee-derived
        /// federation_id; it prevents auxiliary genesis identities from being
        /// byte-reused by two otherwise distinct federations.
        #[arg(long)]
        deployment_domain: Option<String>,

        /// Do not seed the generic faucet, demo agents, default Starbridge
        /// cells, or any positive/negative value.  The genesis contains only
        /// zero-balance, deployment-local issuer and fee wells.  Intended for
        /// application federations (such as Path of Angels) that define their
        /// own assets and must not inherit the generic devnet economy.
        #[arg(long)]
        no_demo_economy: bool,
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
        /// ML-DSA-65 public key(s) for a HYBRID federation, one per `--pubkey`
        /// (positionally aligned; hex, printed by `gen-validator-key`). Omit for a
        /// legacy Ed25519-only federation. A hybrid federation REQUIRES this for
        /// every new validator so the committee identity stays the coupled-core
        /// hybrid roster (the reroll re-derives the same federation_id genesis and
        /// the running node do).
        #[arg(long = "ml-dsa-pubkey")]
        ml_dsa_pubkeys: Vec<String>,
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

    /// Approve a pending membership proposal on this RUNNING node — the ADMIT
    /// half of the live epoch transition (`propose-epoch-transition` / a
    /// joiner's auto-proposed Join registers it; each committee operator runs
    /// THIS until the current committee's quorum is reached). Applies live: no
    /// genesis re-roll, no restart, no federation_id change. List pending
    /// proposals: `curl -s localhost:8420/api/membership`.
    ApproveMembership {
        /// The 64-hex proposal block id (from GET /api/membership).
        #[arg(long)]
        proposal: String,
        /// Running node's HTTP API port.
        #[arg(long, default_value = "8420")]
        port: u16,
        /// Bearer token for the node API (omit on a loopback node with no passphrase).
        #[arg(long)]
        token: Option<String>,
        /// Emit JSON.
        #[arg(long)]
        json: bool,
    },
}

/// Arm the verified-Lean distributed coordination gates (coord / captp / federation / intent).
///
/// Those four crates are FFI-free and route their verified decisions through their own
/// `verified_gate` seams; this installs the Lean-backed impls from `dregg-exec-lean` (the single
/// FFI boundary). `OnceLock`-backed and idempotent — the first registration wins, a second call is
/// a no-op — so every entry into a node may call it unconditionally.
///
/// ⚑ WHY THIS IS NOT INLINE IN [`run`] ANY MORE (2026-07-26). `run` is the CLI entry, and it was
/// the ONLY caller of `register_distributed_gates()` in this crate. Every OTHER way to obtain a
/// node — [`crate::state::NodeState::new`], the in-process axum router, an embedder linking
/// `dregg-node` as a library, and this crate's own test suite — therefore ran with all four seams
/// UNREGISTERED, which is not a loud failure but a silent change of disposition:
///
/// * `dregg-coord`'s 2PC `evaluate_votes` FAILS CLOSED with no gate, so EVERY multi-party
///   proposal decided `Abort` on the first vote — a coordinator that can never commit; and
/// * `dregg-intent`'s `verified_settle::settle_leg` refuses with
///   `verified-executor FFI unavailable: no verified gate registered`, so an intent that should
///   commit through the verified ledger returned 422 at the HTTP seam.
///
/// Both were visible only as test failures in this crate, and both are the deployed behaviour of
/// any embedder that does not go through the CLI. Constructing a node now arms the gates.
pub fn install_verified_distributed_gates() {
    dregg_exec_lean::register_distributed_gates();
}

/// Arm the verified-Lean DEPLOYED-EXECUTOR oracles — the CONSTRAINT oracle (the deployed
/// `StateConstraint`/`HeapAtom` subset decided by the proven `dregg_constraint_admits`) and the
/// CONSERVATION oracle (per-asset `Σδ=0` decided by the proven `dregg_cross_cell_conserves`).
/// Idempotent (both registrations are `OnceLock`-backed), so every entry into a node may call it.
///
/// ⚑ SAME SHAPE AS [`install_verified_distributed_gates`], ONE LAYER DOWN, and it was missed when
/// that one was fixed (2026-07-26): the two oracle registrations were still inline in [`run`], so
/// the distributed gates got armed by [`crate::state::NodeState::new`] while the oracles did not.
/// The dispositions do not match in severity, which is why this matters more than the tidiness:
///
/// * with no CONSTRAINT oracle, `dregg_cell::program::eval` FAILS CLOSED for the whole Lean subset
///   on a native release build (`constraint_subset_fails_closed_without_oracle`), so an embedder that
///   builds a node through `NodeState::new` could serve nothing programmed — it can only refuse; and
/// * with no CONSERVATION oracle the executor does NOT fail closed — it silently decides `Σδ=0`
///   with the unverified Rust twin that already drifted into an inflation bug.
///
/// This installs unconditionally (not release-gated, unlike the SDK's `AgentRuntime` arming): a node
/// is always native and always the deployed configuration, and [`run`] has depended on the debug
/// install for `assert_conservation_oracle_installed` since it was written.
pub fn install_verified_executor_oracles() {
    // The deployed executor's pure-subset admission, computed BY the Lean source
    // (`Dregg2.Exec.DeployedConstraint.admits`) rather than `eval.rs`'s hand-authored Rust `match`.
    // `dregg-cell`/`dregg-turn` cannot link the archive (wasm32 + SP1 zkVM guest), so the backend
    // comes from `dregg-exec-lean` at native startup. When the archive lacks the export (a stale or
    // `DREGG_REQUIRE_LEAN=0` build) this is a no-op — and on a release build every programmed-cell
    // turn then refuses. Such a build cannot boot a node anyway: the SAME missing archive leaves the
    // conservation oracle absent, and `assert_conservation_oracle_installed()` in `run` panics on it.
    if dregg_exec_lean::register_constraint_oracle() {
        tracing::debug!("constraint oracle: verified Lean deployed-constraint evaluator installed");
    }
    // Per-asset `Σδ=0` via `Dregg2.Circuit.CrossCellConserveDecision.conservesFFI`, proved EQUAL to
    // the committed `CrossCellConservation` AIR boundary by
    // `CrossCellConserveRefine.decision_conserves_iff_air_boundary`, replacing the hand-written
    // `dregg_circuit::block_conservation::BlockConservation` twin.
    if dregg_exec_lean::register_conservation_oracle() {
        tracing::debug!(
            "conservation oracle: verified Lean cross-cell per-asset Σδ=0 decision installed"
        );
    }
}

/// Run the node from a parsed [`Cli`]. This is the library entry point the thin
/// `main.rs` binary calls after `Cli::parse()`. It installs process-wide runtime
/// facilities (the rustls crypto provider, the verified-Lean distributed gates,
/// and tracing) and then dispatches the chosen subcommand.
pub async fn run(cli: Cli) {
    // Install the ring CryptoProvider for rustls (required by quinn/QUIC).
    rustls::crypto::ring::default_provider()
        .install_default()
        .expect("failed to install rustls CryptoProvider");

    install_verified_distributed_gates();

    // Arm the verified-Lean deployed-executor oracles (constraint + conservation). One named
    // installer, shared with `NodeState::new` — see `install_verified_executor_oracles` for why the
    // inline copy that used to live here was the same class of bug as the distributed gates above.
    install_verified_executor_oracles();

    // FAIL-CLOSED (twin-deletion #1, gap #2): a native full-Lean node MUST decide per-asset
    // conservation with the verified Lean oracle installed above. If registration was a no-op
    // (missing/stale `libdregg_lean.a`, or the archive lacks the `dregg_cross_cell_conserves`
    // export), the executor would otherwise silently fall through to the UNVERIFIED Rust
    // `BlockConservation` twin — the asset-blind decision that already drifted into an inflation
    // bug. Refuse to boot instead of running the drifting twin. On the wasm32 / zkVM guest this is
    // a no-op (that build's fallback is the legitimate no-Lean path), but the node is always native.
    dregg_turn::executor::assert_conservation_oracle_installed();

    // Initialize tracing. Write to stderr so the MCP stdio subcommand (which
    // serves JSON-RPC on stdout) doesn't get corrupted by log lines.
    tracing_subscriber::fmt()
        .with_writer(std::io::stderr)
        .with_env_filter(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| "dregg_node=info".into()),
        )
        .init();

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
            dev_unlock,
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
                dev_unlock,
            )
            .await
        }
        Command::Init { data_dir } => init::init_node(&data_dir),
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
            deployment_domain,
            no_demo_economy,
        } => genesis::run_genesis_with_options(
            validators,
            epoch_length,
            checkpoint_interval,
            &output,
            genesis::GenesisOptions {
                deployment_domain,
                seed_demo_economy: !no_demo_economy,
            },
        ),
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
            // This command derives the committee's ML-DSA public key from node.key.
            // It is a separate process from `genesis`, so the verified PQ cores
            // installed there do not carry over.  Install before derivation and
            // let dregg-pq fail closed if the linked Lean archive is incomplete.
            install_verified_pq_cores();
            if let Err(e) = operator_join::gen_validator_key(&data_dir, json) {
                eprintln!("error: {e}");
                std::process::exit(1);
            }
        }
        Command::AddValidator {
            pubkeys,
            ml_dsa_pubkeys,
            data_dir,
            json,
        } => {
            if let Err(e) = operator_join::add_validator(&data_dir, &pubkeys, &ml_dsa_pubkeys, json)
            {
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
        Command::ApproveMembership {
            proposal,
            port,
            token,
            json,
        } => {
            if let Err(e) =
                operator_join::approve_membership(port, token.as_deref(), &proposal, json).await
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
                false,
            )
            .await
        }
    }
}

/// Install ALL SIX Lean-verified post-quantum cores as this process's PQ authority — the one
/// named place that does it, so an entry point gets them by CALLING THIS, not by remembering to
/// copy the block.
///
/// ⚑ WHY THIS IS A FUNCTION NOW. These installs used to sit INLINE in `run_node` and nowhere else,
/// so "the deployed node runs verified PQ" was a property of one code path rather than of the
/// binary. `dregg-node genesis` — the documented cold-start step, `scripts/run-node-10min.sh`'s
/// first action — never ran them, so minting the committee ML-DSA key hit `dregg_pq::audit`'s
/// fail-closed refusal and the command died with `Abort trap: 6`. That is cause #3 in the gate's
/// own message, "a host binary that simply never calls the install functions", and it broke cold
/// start at HEAD. `run_mcp` and `run_relay` are the same shape and are now covered too.
///
/// Idempotent and once-per-process; every install is export-gated, so an archive missing a core
/// still installs nothing and the refusal at the point of use still stands. Safe to call from
/// every entry point, and it should be called from every entry point.
pub fn install_verified_pq_cores() {
    // ── ML-DSA VERIFY: install the Lean-verified core as the accept/reject AUTHORITY ──
    // `dregg_pq::ml_dsa_verify` is the security-critical ML-DSA-65 verify behind ~10 surfaces
    // (token/revocation, lightclient, cell-crypto, wire, turn/authorize, captp, blocklace/pq). It is a
    // LIGHT leaf that cannot itself link the 195 MB Lean archive, so it routes through an install-time
    // function pointer: with a REAL core installed it computes the verdict from the extracted, full-byte
    // `MlDsaVerifyReal.verifyCore` (BRICK 8 — proved to accept a genuine `fips204` signature and reject
    // tampers) and NEVER consults the `fips204` crate, taking that crate OUT of the node's verify TCB.
    // Nothing else installs it, so the live node had been falling through to the crate at every verify;
    // this is the wiring that closes that gap — mirroring how the strand-admit / finality / tau-order
    // verified cores are made authoritative above.
    //
    // Gated on `fips204_verify_real_core_available()` (inside `install_mldsa_verified_verify_core`):
    // install ONLY when the linked archive actually EXPORTS `dregg_fips204_verify_real`. A stale archive
    // lacking it would make the installed core return `None` on every call and — because `ml_dsa_verify`
    // fails CLOSED on a core fault (see `dregg-pq/src/mldsa.rs`:
    // `matches!(core(&wire).as_deref(), Some("1"))`) — reject every signature. So when the export is
    // absent we keep the `fips204`-crate fallback (a valid FIPS-204 verify) rather than bricking verify.
    match install_mldsa_verified_verify_core() {
        MlDsaVerifyCoreInstall::Installed => info!(
            "ML-DSA verify: verified Lean core installed — the extracted full-byte \
             `MlDsaVerifyReal.verifyCore` is now the accept/reject authority; the `fips204` crate is no \
             longer the verify authority (out of the node's verify TCB)"
        ),
        MlDsaVerifyCoreInstall::AlreadyInstalled => info!(
            "ML-DSA verify: a verified Lean core was already installed this process (install is \
             once-per-process) — the `fips204` crate remains out of the verify TCB"
        ),
        MlDsaVerifyCoreInstall::ExportAbsent => announce_unverified_pq_site(
            dregg_pq::PqSite::MlDsaVerify,
            "the linked Lean archive does NOT export `dregg_fips204_verify_real`              (`fips204_verify_real_core_available()` is false), so `dregg_pq::ml_dsa_verify` has no              Lean-verified core to route its accept/reject through.",
        ),
    }

    // ── ML-DSA SIGN: install the extracted Lean-verified SCALAR sign core behind `ml_dsa_sign_core` ──
    // ⚠ HONEST SCOPE — this is NOT the sign-side twin of the verify install above. The verify install wires
    // BRICK 8's FULL-BYTE `MlDsaVerifyReal.verifyCore` as the authority behind the DEPLOYED byte-level
    // `dregg_pq::ml_dsa_verify`, taking the `fips204` crate out of the verify TCB. The sign core available
    // today is only the SCALAR (n=1) `Fips204Verify.signCore` — a 5-int→3-int Fiat–Shamir-with-aborts
    // object. Installing it makes that verified scalar object the backend of `dregg_pq::ml_dsa_sign_core`
    // (the scalar-model seam); it does NOT route the deployed `MlDsaKey::sign` byte-level signer, which
    // STILL calls the `fips204` crate. So this install does NOT remove the crate from the node's SIGN TCB.
    // The real full-byte sign core — the same 8-brick build the verify side got (SHAKE/ring/samplers reused,
    // adding MakeHint + the rejection loop) — is the named follow-up. We wire the scalar core here so the
    // verified sign object runs LIVE in the deployed binary and its sign→verify round-trip is exercised
    // (see `tests/mldsa_live_sign.rs`).
    match install_mldsa_verified_sign_core() {
        MlDsaSignCoreInstall::Installed => info!(
            "ML-DSA sign: verified Lean SCALAR sign core installed behind `ml_dsa_sign_core` — the \
             extracted `Fips204Verify.signCore` (n=1 model, proved to agree with the spec) now runs live. \
             NOTE: the deployed byte-level `MlDsaKey::sign` STILL uses the `fips204` crate — the crate has \
             NOT left the node's SIGN TCB. The real full-byte sign core is the named follow-up."
        ),
        MlDsaSignCoreInstall::AlreadyInstalled => info!(
            "ML-DSA sign: a Lean scalar sign core was already installed this process (install is \
             once-per-process)"
        ),
        MlDsaSignCoreInstall::ExportAbsent => announce_unverified_pq_site(
            dregg_pq::PqSite::MlDsaSign,
            "the linked Lean archive does NOT export `dregg_fips204_sign`              (`fips204_sign_core_available()` is false), so the SCALAR verified sign object does not              run live and `ml_dsa_sign_core` returns None.",
        ),
    }

    // ── ML-DSA SIGN (REAL): install the Lean-verified REAL, FULL-BYTE sign core as `MlDsaKey::sign`'s
    // PRODUCER — the sign-side twin of the verify install above (BRICK 8 SIGN analog). ──
    // With a REAL core installed, the DEPLOYED byte-level signer `dregg_pq::MlDsaKey::sign` (and
    // `ml_dsa_sign_from_seed`) PRODUCES the 3309-byte signature from the extracted, full-dimension
    // `MlDsaSignReal.signCore` (proved byte-exact vs the `fips204` crate's deterministic signature) over the
    // real `sk ‖ msg ‖ ctx` bytes — and NEVER consults the `fips204` crate, taking that crate OUT of the
    // node's SIGN TCB. On this path the signer is DETERMINISTIC (`rnd = 0`, the FIPS 204 deterministic
    // variant — spec-valid). Gated on `fips204_sign_real_core_available()`: install ONLY when the linked
    // archive actually EXPORTS `dregg_fips204_sign_real`; a stale archive lacking it keeps the hedged
    // `fips204`-crate fallback (a valid FIPS-204 sign) rather than bricking sign.
    match install_mldsa_verified_sign_core_real() {
        MlDsaSignCoreRealInstall::Installed => info!(
            "ML-DSA sign: verified Lean REAL sign core installed — the extracted full-byte \
             `MlDsaSignReal.signCore` is now the PRODUCER behind the deployed `MlDsaKey::sign`; the \
             `fips204` crate is no longer the signing authority (out of the node's SIGN TCB). Signing is \
             now DETERMINISTIC (rnd=0, the FIPS 204 deterministic variant)."
        ),
        MlDsaSignCoreRealInstall::AlreadyInstalled => info!(
            "ML-DSA sign: a verified Lean REAL sign core was already installed this process (install is \
             once-per-process) — the `fips204` crate remains out of the SIGN TCB"
        ),
        MlDsaSignCoreRealInstall::ExportAbsent => announce_unverified_pq_site(
            dregg_pq::PqSite::MlDsaSign,
            "the linked Lean archive does NOT export `dregg_fips204_sign_real`              (`fips204_sign_real_core_available()` is false), so the deployed `MlDsaKey::sign` has no              Lean-verified producer for the signature bytes it puts on the wire.",
        ),
    }

    // ── ML-DSA KEYGEN: install the REAL full-byte core behind identity-key derivation ──
    // This is the same shared install seam used by SDK hosts. The extracted core deterministically expands
    // the 32-byte identity seed into the FIPS 204 ML-DSA-65 keypair; it is KAT-anchored byte-exact against
    // NIST ACVP vectors (the byte↔ring refinement forall remains open). Without this install, key generation
    // now refuses unless the operator explicitly accepts the unaudited crate fallback.
    match install_mldsa_verified_keygen_core_real() {
        MlDsaKeygenCoreRealInstall::Installed => info!(
            "ML-DSA keygen: verified Lean core installed — the extracted full-byte keygen is now the \
             identity-key expander; the `fips204` crate is out of the node's keygen TCB"
        ),
        MlDsaKeygenCoreRealInstall::AlreadyInstalled => {
            info!("ML-DSA keygen: a verified Lean core was already installed this process")
        }
        MlDsaKeygenCoreRealInstall::ExportAbsent => announce_unverified_pq_site(
            dregg_pq::PqSite::MlDsaKeygen,
            "the linked Lean archive does NOT export `dregg_mldsa_keygen_real`, so the node IDENTITY              key has no Lean-verified expander. This is the one keygen that mints LONG-LIVED key              material, and it REFUSES rather than warning (unlike the ephemeral ML-KEM keygen).",
        ),
    }

    // ── ML-KEM DECAPS: install the Lean-verified REAL core as `HybridResponder::finish`'s AUTHORITY ──
    // The hybrid session KEM (`dregg_pq::hybrid_kem`) recovers the ML-KEM-768 shared secret on the responder
    // side by calling the `ml-kem` crate's `.decapsulate`. With a REAL core installed it instead recovers the
    // secret from the extracted, full-byte `Dregg2.Crypto.MlKemDecaps.mlkemDecaps` (BRICK K6 — the FO pipeline
    // proved to recover a genuine crate secret and implicit-reject tampers to a DIFFERENT secret) and NEVER
    // consults the `ml-kem` crate, taking that crate OUT of the node's KEM-decaps TCB. The X25519 + transcript
    // + HKDF combiner around the ML-KEM secret is unchanged — only the `.decapsulate` call is replaced.
    //
    // Gated on `mlkem_decaps_real_core_available()`: install ONLY when the linked archive actually EXPORTS
    // `dregg_mlkem_decaps_real`. A stale archive lacking it would make `finish` fail CLOSED on every
    // ciphertext, so when the export is absent we keep the `ml-kem`-crate fallback (a valid FIPS-203 decaps).
    match install_mlkem_verified_decaps_core() {
        MlKemDecapsCoreInstall::Installed => info!(
            "ML-KEM decaps: verified Lean core installed — the extracted full-byte \
             `MlKemDecaps.mlkemDecaps` is now the shared-secret authority behind `HybridResponder::finish`; \
             the `ml-kem` crate is no longer the decaps authority (out of the node's KEM-decaps TCB)"
        ),
        MlKemDecapsCoreInstall::AlreadyInstalled => info!(
            "ML-KEM decaps: a verified Lean core was already installed this process (install is \
             once-per-process) — the `ml-kem` crate remains out of the KEM-decaps TCB"
        ),
        MlKemDecapsCoreInstall::ExportAbsent => announce_unverified_pq_site(
            dregg_pq::PqSite::MlKemDecaps,
            "the linked Lean archive does NOT export `dregg_mlkem_decaps_real`              (`mlkem_decaps_real_core_available()` is false), so the session shared secret behind              `HybridResponder::finish` is recovered with no Lean-verified authority.",
        ),
    }

    // ── ML-KEM ENCAPS: install the Lean-verified REAL core as `hybrid_kem::initiate`'s AUTHORITY ──
    // The hybrid session KEM initiator (`dregg_pq::hybrid_kem::initiate`) produces the ML-KEM-768 ciphertext +
    // shared secret by calling the `ml-kem` crate's `.encapsulate`. With a REAL core installed it instead
    // produces them from the extracted, full-byte `Dregg2.Crypto.MlKemEncaps.mlkemEncaps` (BRICK K5 — the
    // deterministic FO encaps proved BYTE-EXACT vs the crate's `EncapsulateDeterministic`) and NEVER consults
    // the `ml-kem` crate, taking that crate OUT of the node's KEM-encaps TCB. The initiator supplies its own
    // 32-byte `m` (fresh OS entropy, as the crate does internally); the X25519 + transcript + HKDF combiner is
    // unchanged. This closes the LAST deployed crypto direction: after it, no deployed process trusts
    // `fips204`/`ml-kem` for any security-critical direction.
    //
    // Gated on `mlkem_encaps_real_core_available()`: install ONLY when the linked archive actually EXPORTS
    // `dregg_mlkem_encaps_real`. When the export is absent we keep the `ml-kem`-crate fallback (a valid encaps).
    match install_mlkem_verified_encaps_core() {
        MlKemEncapsCoreInstall::Installed => info!(
            "ML-KEM encaps: verified Lean core installed — the extracted full-byte \
             `MlKemEncaps.mlkemEncaps` is now the ciphertext+secret authority behind `hybrid_kem::initiate`; \
             the `ml-kem` crate is no longer the encaps authority (out of the node's KEM-encaps TCB)"
        ),
        MlKemEncapsCoreInstall::AlreadyInstalled => info!(
            "ML-KEM encaps: a verified Lean core was already installed this process (install is \
             once-per-process) — the `ml-kem` crate remains out of the KEM-encaps TCB"
        ),
        MlKemEncapsCoreInstall::ExportAbsent => announce_unverified_pq_site(
            dregg_pq::PqSite::MlKemEncaps,
            "the linked Lean archive does NOT export `dregg_mlkem_encaps_real`              (`mlkem_encaps_real_core_available()` is false), so the session ciphertext+secret from              `hybrid_kem::initiate` is produced with no Lean-verified authority.",
        ),
    }

    // ── ML-KEM KEYGEN: install the REAL full-byte core behind hybrid responder offers ──
    // `responder_offer` now routes through the shared bare-keygen authority instead of minting a crate key
    // directly. Installing here therefore covers the actual CaPTP/session handshake as well as bare KEM users.
    match install_mlkem_verified_keygen_core() {
        MlKemKeygenCoreInstall::Installed => info!(
            "ML-KEM keygen: verified Lean core installed — hybrid responder keypairs now come from the \
             extracted full-byte keygen; the `ml-kem` crate is out of the node's KEM-keygen TCB"
        ),
        MlKemKeygenCoreInstall::AlreadyInstalled => {
            info!("ML-KEM keygen: a verified Lean core was already installed this process")
        }
        MlKemKeygenCoreInstall::ExportAbsent => announce_unverified_pq_site(
            dregg_pq::PqSite::MlKemKeygen,
            "the linked Lean archive does NOT export `dregg_mlkem_keygen_real`, so hybrid responder              keypairs are minted with no Lean-verified expander. ⚑ THIS ONE WARNS AND PROCEEDS EVEN              UNDER DREGG_REQUIRE_LEAN=1 (a DECLARED exception, see dregg_pq::audit::             guard_no_verified_core): the key is EPHEMERAL per-session material and refusing bricks              every CaPTP/session handshake on an archive-less process.",
        ),
    }
}

/// Call [`install_verified_pq_cores`] at process start in the LIB-TEST binary.
///
/// The five callers of `install_verified_pq_cores` — `run_node`, `run_genesis`,
/// `gen-validator-key`, `run_mcp`, and `run_relay` — are all BINARY entry points.
/// `cargo test -p dregg-node --lib` runs none of them, so the lib-test process had no verified
/// core installed and `dregg_pq::audit` did the
/// only correct thing on the first ML-DSA keygen: `process::abort()`. An abort kills the
/// process, so that took down all 506 tests in the binary, not just the one that minted a key.
/// The only way anyone had got results out of it was `DREGG_ALLOW_UNAUDITED_PQ=1`, which routes
/// keygen onto the `fips204` crate — the substitution the audit gate exists to prevent, and a
/// reason to distrust every verdict obtained that way.
///
/// There is no `main` in a libtest binary to hang the call on, and no single derivation point
/// inside this crate to install at: node's tests mint ML-DSA keys from ~30 files through four
/// different crates (`dregg_blocklace::finality::Block`,
/// `dregg_federation::frost::MlDsaSigningKey`, `dregg_turn::pq::MlDsaTurnKey`,
/// `dregg_sdk::cipherclerk`). A process-start initializer is the one place that covers all of
/// them, and it puts the test process in the same disposition as the deployed binary: verified
/// cores installed before the first PQ operation, fail-closed if the archive lacks them.
///
/// `#[cfg(test)]`, so the shipped library carries no initializer. The install is export-gated
/// and once-per-process, so the handful of tests that already call the per-core installs
/// themselves (`blocklace_sync.rs`) just see `AlreadyInstalled`.
#[cfg(all(test, any(target_os = "linux", target_os = "macos")))]
mod pq_test_bootstrap {
    extern "C" fn install() {
        super::install_verified_pq_cores();
    }

    #[used]
    #[cfg_attr(target_os = "linux", unsafe(link_section = ".init_array"))]
    #[cfg_attr(target_os = "macos", unsafe(link_section = "__DATA,__mod_init_func"))]
    static INSTALL_VERIFIED_PQ_CORES: extern "C" fn() = install;
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
    dev_unlock: bool,
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
    //
    // The refusal must also be SIDE-EFFECT-FREE, so it runs HERE — before
    // `NodeState` construction touches the data dir. When it ran after state
    // construction + devnet seeding, a refused first launch left a partially
    // initialized data dir: the relaunch (with the opt-in set) took the
    // recovery path instead of the fresh-boot path and never provisioned the
    // operator's agent cell. The first `/api/faucet` call without `public_key`
    // then materialized that cell as a zero-key stub, and every signed turn on
    // that data dir failed "Ed25519 signature verification failed" forever
    // (the faucet never rewrites an existing cell's key). Reproduced
    // end-to-end: clean boot → agent cell present with the operator key;
    // refused-launch-then-relaunch → agent cell absent.
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

    // Every PQ core this process will answer with, installed before anything mints, signs, or
    // serves. See `install_verified_pq_cores` for why this is one call and not 180 inline lines.
    install_verified_pq_cores();

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
    let mut consensus_time_policy_v1 = None;
    let genesis_path = data_path.join("genesis.json");
    if genesis_path.exists() {
        match std::fs::read_to_string(&genesis_path) {
            Ok(json_str) => {
                match serde_json::from_str::<serde_json::Value>(&json_str) {
                    Ok(genesis) => {
                        match blocklace_sync::consensus_time_policy_v1_from_genesis(&genesis) {
                            Ok(policy) => consensus_time_policy_v1 = Some(policy),
                            Err(error) => error!(
                                error = %error,
                                "genesis.json does not carry a valid explicit consensus-time-v1 policy"
                            ),
                        }
                        let mut s = node_state.write().await;
                        // Set committee_epoch BEFORE loading keys so the
                        // first federation_id derivation uses the correct
                        // epoch.
                        if let Some(ce) = genesis["committee_epoch"].as_u64() {
                            s.committee_epoch = ce;
                        }
                        // Extract validator public keys from genesis — the
                        // ed25519 committee AND (HYBRID-PQ) each member's
                        // published ML-DSA-65 key, INDEX-ALIGNED. If ANY
                        // validator lacks a decodable `ml_dsa_public_key`, the
                        // whole ML-DSA vec is left empty: hybrid is then
                        // unconfigured and the vote collector counts no votes
                        // (fail-closed — never a partial/misaligned committee).
                        if let Some(validators) = genesis["validators"].as_array() {
                            let mut fed_keys = Vec::new();
                            let mut ml_dsa_keys = Vec::new();
                            let mut ml_dsa_complete = true;
                            for v in validators {
                                if let Some(pk_hex) = v["public_key"].as_str()
                                    && let Some(pk_bytes) = hex_decode_32(pk_hex)
                                {
                                    fed_keys.push(dregg_types::PublicKey(pk_bytes));
                                    match v["ml_dsa_public_key"]
                                        .as_str()
                                        .and_then(parse_ml_dsa_public_key)
                                    {
                                        Some(k) => ml_dsa_keys.push(k),
                                        None => ml_dsa_complete = false,
                                    }
                                }
                            }
                            if !fed_keys.is_empty() {
                                let ml_dsa_keys = if ml_dsa_complete {
                                    ml_dsa_keys
                                } else {
                                    tracing::warn!(
                                        "genesis.json is missing (or has undecodable) \
                                         ml_dsa_public_key entries — HYBRID-PQ finality is \
                                         UNCONFIGURED and finalization votes will not count \
                                         (fail-closed); re-mint genesis to enable it"
                                    );
                                    Vec::new()
                                };
                                info!(
                                    key_count = fed_keys.len(),
                                    ml_dsa_keys = ml_dsa_keys.len(),
                                    "loaded federation keys from genesis.json"
                                );
                                s.set_federation_keys_hybrid(fed_keys, ml_dsa_keys);
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
                        // Post-checkpoint removals (MakeSovereign tombstones) that
                        // the genesis baseline would otherwise resurrect.
                        let removed_since_checkpoint = {
                            let cp_h = s.store.latest_ledger_checkpoint_height().unwrap_or(0);
                            s.store.removed_cell_ids_since(cp_h).unwrap_or_default()
                        };
                        let cell_load = reseed_genesis_then_overlay(
                            &genesis,
                            &mut s.ledger,
                            &removed_since_checkpoint,
                        );
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
                                // The well backs the asset it is MINTED IN — read
                                // it off the materialized cell instead of assuming
                                // a domain. `issuer_well_for` looks the well up by
                                // the burning cell's `token_id`, so registering the
                                // well under the wrong asset silently unregisters
                                // it (burns fall back to the lazily-derived well and
                                // the genesis −supply account is orphaned). This
                                // read is also what lets a data dir written by an
                                // older genesis (all-zero domain) keep working.
                                Some(id) => {
                                    let well_id = dregg_cell::CellId(id);
                                    let token_id = s
                                        .ledger
                                        .get(&well_id)
                                        // The well is REGISTERED UNDER ITS ASSET
                                        // (`TurnExecutor::issuer_well_for` keys on
                                        // `Cell::asset`), never under its name salt.
                                        .map(|cell| *cell.asset().as_bytes())
                                        .unwrap_or_else(crate::executor_setup::default_token_id);
                                    s.issuer_wells.push((token_id, well_id));
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
        // THE FEE LOOP (revolving fund): a genesis-less devnet cave node never
        // hits the `genesis.json`-exists branch above (lib.rs:1229-1236), so
        // `s.fee_well` is still None here — which means every per-turn fee
        // remainder BURNS (execute.rs distribute_fee_shares fallback), and the
        // faucet, a pure payer-out, drains monotonically (~800-turn runway →
        // "insufficient balance ... need 1254" → signing DEGRADED). Point the
        // fee well at the FAUCET cell so each committed turn's fee move
        // recirculates into the exact pool the faucet pays out of: the
        // {agents + faucet} value set is now closed (no external sink), payouts
        // out are offset by fees in, and the coordination-turn class stays
        // fee-bearing (the debit + budget gate + 1/min faucet rate-limit remain
        // the oversight leash — no fee is zeroed). Idempotent: only sets the
        // well when unset, so a genesis-configured well is never overwritten.
        if s.fee_well.is_none() {
            let faucet_cell_id = crate::api::faucet_cell_id();
            info!(
                fee_well = %faucet_cell_id,
                "fee loop: genesis-less devnet fee well pointed at the faucet cell (recirculate, not burn)"
            );
            s.fee_well = Some(faucet_cell_id);
        }
    }

    // Demo execution-lease seed — the local-cloud loop's mint. An external
    // provider decodes a lease off `GET /api/cell/{id}` only when the cell is
    // program-bearing with the lease slots sealed (RENT/PERIOD/PROVIDER) and a
    // funded balance — and program install is not a wire effect, so no HTTP
    // client can create one. Dev-gated twice (`--enable-faucet` AND
    // `DREGG_SEED_DEMO_LEASE=1`); insert-if-absent on every boot.
    //
    // FEDERATION-WIDE by construction: both the lease cell and its provider
    // (rent beneficiary) derive from the FEDERATION_ID, not from this node's
    // operator key. Every validator in the federation therefore seeds the
    // IDENTICAL pair — same ids, same program, same sealed slots — so a
    // settlement turn ordered by consensus applies on every replica. (Keying
    // them off the per-node operator instead gave each validator its own private
    // lease: consensus ran, but the workload was node-local state that the other
    // replicas had never heard of.) The balance IS the prepaid budget the
    // provider meters against; rent 1 per 60-block period, open-ended.
    if enable_faucet && std::env::var("DREGG_SEED_DEMO_LEASE").as_deref() == Ok("1") {
        use starbridge_execution_lease as lease_app;
        let mut s = node_state.write().await;
        let operator_pubkey = s.cclerk.public_key().0;
        let native = [0u8; 32];
        let federation_id = s.federation_id;
        // The LEASE is OPERATOR-OWNED (per-node). The metered settlement is a plain
        // operator-signed Transfer FROM the lease, so the operator must OWN it — a
        // lease owned by some other key refuses the transfer ("Ed25519 signature
        // half failed"). This makes the lease node-local; a genuinely
        // federation-wide lease whose rent settles on every replica needs the
        // lease PROGRAM's metered discharge (pay/advance) instead of a plain
        // operator Transfer, which is a real integration step — see
        // docs/FINDING-federation-wide-settlement.md.
        let lease_pubkey = operator_pubkey;
        // The PROVIDER (rent beneficiary) IS federation-wide: a real Ed25519 key
        // derived deterministically from the federation id, so every replica seeds
        // the identical cell and a settlement Transfer credits a cell they all hold.
        let provider_pubkey = ed25519_dalek::SigningKey::from_bytes(&blake3::derive_key(
            "dregg-demo-lease-provider-v1",
            &federation_id,
        ))
        .verifying_key()
        .to_bytes();
        let lease_id = dregg_cell::CellId::derive_raw(&lease_pubkey, &native);
        let provider_cell = dregg_cell::CellId::derive_raw(&provider_pubkey, &native);
        if s.ledger.get(&lease_id).is_none() {
            let operator_cell = dregg_cell::CellId::derive_raw(
                &operator_pubkey,
                blake3::hash(b"default").as_bytes(),
            );
            // The rent beneficiary — seeded empty, identical on every replica, so
            // the metered settlement Transfer credits a cell all replicas hold.
            if s.ledger.get(&provider_cell).is_none() {
                let pcell = dregg_cell::Cell::with_balance(provider_pubkey, native, 0);
                if let Err(e) = s.ledger.insert_cell(pcell) {
                    warn!(error = %e, "demo lease provider cell insert failed");
                }
            }
            let mut cell = dregg_cell::Cell::with_balance(lease_pubkey, native, 10_000);
            cell.program = lease_app::lease_cell_program();
            let terms = lease_app::LeaseTerms::new(
                provider_cell,
                lease_id,
                dregg_cell::CellId(native),
                1,
                60,
                0,
                0,
            );
            match lease_app::open_lease(&mut cell, &terms, lease_app::field_from_u64(0)) {
                Ok(()) => match s.ledger.insert_cell(cell) {
                    Ok(id) => {
                        // Give the operator c-list reach + set_state on the lease
                        // so it can author the exec-lease GRANT turn an external
                        // provider's verified read decodes (same as the starbridge
                        // seeder does for its factory cells).
                        starbridge_seed::grant_operator_reach(
                            &mut s.ledger,
                            operator_cell,
                            operator_pubkey,
                            id,
                        );
                        info!(
                            lease = %dregg_types::hex_encode(&id.0),
                            provider = %dregg_types::hex_encode(&provider_cell.0),
                            budget = 10_000,
                            "seeded demo execution-lease (funded, federation-wide, operator-reachable)"
                        );
                    }
                    Err(e) => warn!(error = %e, "demo execution-lease insert failed"),
                },
                Err(e) => warn!(error = ?e, "demo execution-lease open refused"),
            }
        }
    }

    // Derive the committee from the persisted chain BEFORE the recovery anchor
    // runs (`committee_replay`): a live epoch transition amends the committee
    // ON-CHAIN without changing the `federation_id`, so (a) the signed-anchor
    // check below must accept an attested-root quorum from any committee the
    // constitution passed through, and (b) the consensus boot must seed the
    // AMENDED constitution — not genesis — or a restart silently reverts the
    // membership (the re-roll trap). A lace with no membership blocks makes
    // this a cheap no-op.
    {
        let mut s = node_state.write().await;
        let sk_bytes = s.cclerk.gossip_signing_key().to_bytes();
        let sk = ed25519_dalek::SigningKey::from_bytes(&sk_bytes);
        let self_key: [u8; 32] = sk.verifying_key().to_bytes();
        let genesis_committee: Vec<[u8; 32]> = if s.known_federation_keys.is_empty() {
            vec![self_key]
        } else {
            s.known_federation_keys.iter().map(|k| k.0).collect()
        };
        let q = dregg_blocklace::supermajority_threshold(genesis_committee.len());
        match s.store.load_blocklace(sk, q) {
            Ok(Some((lace, _))) => {
                let (derived, cm) = committee_replay::derive_from_lace(
                    &lace,
                    &genesis_committee,
                    blocklace_wave_timeout_ms,
                );
                if derived.amendments > 0 {
                    info!(
                        amendments = derived.amendments,
                        version = derived.version,
                        participants = derived.participants.len(),
                        threshold = derived.threshold,
                        "committee derived from chain: finalized membership \
                         amendments survive this restart (no genesis re-roll)"
                    );
                    s.derived_committee_history = derived
                        .history
                        .iter()
                        .map(|c| c.iter().map(|k| dregg_types::PublicKey(*k)).collect())
                        .collect();
                    // The on-chain membership blocklace records only ed25519 keys,
                    // so a chain-derived historical committee has NO enrolled
                    // ML-DSA roster: populate the aligned twin with an EMPTY roster
                    // per entry. The restart hybrid re-verify then REFUSES a root
                    // signed by such a committee (no silent ed25519-only downgrade,
                    // per `verify_finalization_quorum`'s roster-alignment bound).
                    s.derived_committee_ml_dsa_history =
                        derived.history.iter().map(|_| Vec::new()).collect();
                }
                s.boot_constitution = Some(cm);
            }
            Ok(None) => {}
            Err(e) => {
                tracing::warn!(
                    error = %e,
                    "could not load the persisted lace for boot committee derivation — \
                     falling back to the configured (genesis) committee"
                );
            }
        }
    }

    // Recovery-convergence verdict (DEFERRED from NodeState construction), via the
    // ONE weld every serving entrypoint runs. The reseed above already put the
    // genesis baseline under the recovered overlay; `complete_boot_recovery` redoes
    // it idempotently and then renders the verdict. FAIL CLOSED on mismatch.
    if let Err(e) = complete_boot_recovery(&node_state, &data_path, BootBaseline::Complete).await {
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

        // DEVNET BRING-UP: start UNLOCKED with no passphrase so a local devnet
        // demo anchors turns out of the box — no manual /cipherclerk/unlock +
        // bearer dance (that dance is exactly what made every /descent/submit
        // anchor soft-fail 403). This EXTENDS the MCP-stdio auto-unlock precedent
        // (single-user, no remote attacker) to an EXPLICIT, loopback-gated HTTP
        // mode. It is REFUSED — the node stays locked and logs why — unless BOTH:
        //   (1) the operator opted in via --dev-unlock or DREGG_DEV_UNLOCK=1, AND
        //   (2) the node binds a loopback address (127.0.0.1 / ::1), AND
        //   (3) the data dir has NO passphrase set.
        // A network bind (--bind 0.0.0.0) or an already-passphrased data dir keeps
        // the passphrase requirement intact, so a production node is NEVER
        // weakened. With no passphrase set, require_auth admits loopback callers
        // with no bearer, so the same-host web anchors turns with no auth dance.
        let dev_unlock_env = std::env::var("DREGG_DEV_UNLOCK")
            .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
            .unwrap_or(false);
        if dev_unlock || dev_unlock_env {
            let bind_is_loopback = bind
                .parse::<std::net::IpAddr>()
                .map(|ip| ip.is_loopback())
                .unwrap_or(false);
            if !bind_is_loopback {
                tracing::warn!(
                    bind = %bind,
                    "--dev-unlock / DREGG_DEV_UNLOCK requested but --bind is not a loopback \
                     address — REFUSING to auto-unlock a network-exposed node. It stays LOCKED. \
                     Set a passphrase via /cipherclerk/set-passphrase, or bind 127.0.0.1 for a \
                     local devnet demo."
                );
            } else if s.passphrase_hash.is_some() {
                tracing::warn!(
                    "--dev-unlock / DREGG_DEV_UNLOCK requested but this data dir already has a \
                     passphrase set — leaving it passphrase-gated (bearer required). Dev-unlock \
                     only applies to a fresh, passphrase-free devnet data dir."
                );
            } else {
                s.unlocked = true;
                tracing::warn!(
                    "DEV-UNLOCK: cipherclerk started UNLOCKED with NO passphrase (loopback bind, \
                     explicit opt-in). Loopback callers may submit turns with no bearer — devnet \
                     bring-up only. NEVER use this on a network-exposed or production node."
                );
            }
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
    // The full-mode consensus role needs BOTH verified exports: `dregg_tau_order` (the finalized
    // ORDER, twin #8) AND `dregg_finalization_quorum` (the consensus-attested QUORUM decision,
    // twin #11). They are co-located in `Dregg2.Distributed.FinalityGate` (present together), but are
    // probed independently so a future split cannot silently route a live node onto the un-verified
    // Rust `VoteCollector` quorum twin. Requiring both here is what makes the per-vote quorum fallback
    // in `finalization_votes::record` unreachable on a live full node (the export is always present),
    // so the Rust `distinct_votes >= threshold` twin never decides consensus attestation.
    let consensus_exports_linked = dregg_lean_ffi::tau_order_available()
        && dregg_lean_ffi::distributed_ffi::finalization_quorum_available();
    if !is_solo_mode && !consensus_exports_linked {
        // Reuses the `allow_unverified` escape hatch parsed above (the same
        // DREGG_ALLOW_UNVERIFIED_CONSENSUS variable governs both gates).
        if allow_unverified {
            tracing::warn!(
                tau_order = dregg_lean_ffi::tau_order_available(),
                finalization_quorum =
                    dregg_lean_ffi::distributed_ffi::finalization_quorum_available(),
                "VERIFIED-CONSENSUS HARD-CHECK OVERRIDDEN: this node is in FULL (multi-party BFT) \
                 mode but the Lean verified-consensus archive is NOT fully linked (`dregg_tau_order` \
                 and/or `dregg_finalization_quorum` absent). DREGG_ALLOW_UNVERIFIED_CONSENSUS is set, \
                 so the node will proceed on the UN-VERIFIED Rust `ordering::tau` / `VoteCollector` \
                 twins — its finality is NOT shadowed by the verified rule. Do not use this in a \
                 federation that expects verified consensus."
            );
        } else {
            error!(
                tau_order = dregg_lean_ffi::tau_order_available(),
                finalization_quorum =
                    dregg_lean_ffi::distributed_ffi::finalization_quorum_available(),
                "REFUSING TO START: this node is configured for VERIFIED consensus (federation \
                 mode FULL — multi-party BFT finality), but the Lean verified-consensus archive is \
                 not fully linked: `dregg_tau_order` (finalized order) and/or \
                 `dregg_finalization_quorum` (consensus-attested quorum) is absent (e.g. a \
                 marshal-only / stale archive). A verified-role node MUST NOT silently fall back to \
                 the un-verified Rust ordering / quorum twins. Rebuild the node against the \
                 closure-complete verified archive (it splices Dregg2.Distributed.FinalityGate), run \
                 this node in `--federation-mode solo` if it is not meant to finalize, or set \
                 DREGG_ALLOW_UNVERIFIED_CONSENSUS=1 to explicitly accept un-verified consensus."
            );
            std::process::exit(1);
        }
    } else if !is_solo_mode {
        info!(
            "verified-consensus hard-check passed: the Lean `dregg_tau_order` + \
             `dregg_finalization_quorum` archive is linked — this full-mode node finalizes over the \
             VERIFIED ordering + quorum rules"
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
            let consensus_time_policy = consensus_time_policy_v1.unwrap_or_else(|| {
                error!(
                    genesis = %genesis_path.display(),
                    "blocklace requires consensus_genesis_unix_seconds + consensus_time_mode in the shared genesis.json; refusing an implicit clock policy"
                );
                std::process::exit(1);
            });
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
            let blocklace_handle = blocklace_sync::run_blocklace_sync_with_policy(
                sync_state,
                gossip_port_copy,
                auto_approve_joins,
                blocklace_checkpoint_interval,
                blocklace_wave_timeout_ms,
                block_cadence_ms,
                idle_heartbeat_ms,
                min_block_interval_ms,
                advertise_addr,
                consensus_time_policy,
            )
            .await;
            if let Some(handle) = blocklace_handle {
                node_state.set_blocklace(handle).await;
                // Resume any private dependent turn whose durable Ready event
                // preceded this process. The scheduler's destructive redb
                // claim is the at-most-once authority across restart.
                private_dependent_turns::spawn_private_dependent_turn_drain(node_state.clone());
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
    // The MCP tools commit turns, which SIGN. Same install `run_node` does, for the same reason.
    install_verified_pq_cores();

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

    // The SAME boot-recovery weld `run_node` runs. `NodeState::new` renders no
    // integrity verdict (see `complete_boot_recovery`), and the MCP tools COMMIT
    // TURNS — so without this an image whose recorded finalized root the ledger does
    // not reconstruct was served here in silence, on a data dir `run_node` would
    // refuse. `PartialServeOnly`: this path builds no starbridge/demo baseline, so it
    // must never pin one.
    if let Err(e) =
        complete_boot_recovery(&node_state, &data_path, BootBaseline::PartialServeOnly).await
    {
        error!("{e}");
        std::process::exit(1);
    }

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
    // The relay signs delivery proofs and dispute submissions under its operator identity.
    install_verified_pq_cores();

    let data_path = expand_path(data_dir);

    // Read operator key from the data directory.
    let operator_key = if data_path.join("node.key").exists() {
        let key_bytes = std::fs::read(data_path.join("node.key"))
            .expect("failed to read node.key for relay operator identity");
        if key_bytes.len() != 32 {
            error!(
                "node.key in {} is malformed: expected 32 bytes, found {}. \
                 Re-run `dregg-node init`.",
                data_path.display(),
                key_bytes.len()
            );
            std::process::exit(1);
        }
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
            // FAIL CLOSED: no external assets accepted until the operator
            // declares a per-asset table (docs/deos/COMPUTRON-POLICY.md).
            external_assets: Default::default(),
        },
        max_total_capacity: max_capacity,
        gc_interval_secs: gc_interval,
        message_ttl_blocks: message_ttl,
        dispute_window_blocks: relay_service::DEFAULT_DISPUTE_WINDOW_BLOCKS,
        max_delivery_proofs: relay_service::DEFAULT_MAX_DELIVERY_PROOFS,
        max_delivery_latency_blocks: max_delivery_latency,
        state_file,
        default_inbox_capacity,
        default_min_deposit,
    };

    relay_service::run_relay_service(config).await;
}

/// Decode a genesis-published ML-DSA-65 public key: 3904 hex chars → the
/// 1952-byte FIPS 204 serialized key (the array length is inferred from the
/// `MlDsaPublicKey` constructor, so this stays in lockstep with the type).
/// `None` on any length/character violation.
fn parse_ml_dsa_public_key(s: &str) -> Option<dregg_federation::frost::MlDsaPublicKey> {
    if !s.is_ascii() || s.len() % 2 != 0 {
        return None;
    }
    let mut bytes = Vec::with_capacity(s.len() / 2);
    for i in 0..s.len() / 2 {
        bytes.push(u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).ok()?);
    }
    bytes
        .try_into()
        .ok()
        .map(dregg_federation::frost::MlDsaPublicKey)
}

/// Decode an even-length hex string into bytes (used for the variable-length
/// ML-DSA-65 public key a genesis cell commits).
fn hex_decode_vec(s: &str) -> Option<Vec<u8>> {
    if !s.is_ascii() || !s.len().is_multiple_of(2) {
        return None;
    }
    (0..s.len() / 2)
        .map(|i| u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).ok())
        .collect()
}

/// Decode a 64-char hex string into a [u8; 32].
fn hex_decode_32(s: &str) -> Option<[u8; 32]> {
    if !s.is_ascii() || s.len() != 64 {
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
/// Test seam over [`materialize_genesis_cells`] — the REAL boot-time
/// materializer, so `genesis.rs`'s seam test checks what a node actually loads
/// rather than a re-implementation of it. Returns `(inserted, invalid)`.
#[cfg(test)]
pub(crate) fn materialize_genesis_cells_for_test(
    genesis: &serde_json::Value,
    ledger: &mut dregg_cell::Ledger,
) -> (usize, usize) {
    let stats = materialize_genesis_cells(genesis, ledger);
    (stats.inserted, stats.invalid)
}

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
        // THE PQ IDENTITY COMMITMENT. Hybrid admission
        // (`signed_turn_validation::validate_signed_turn`, required-PQ ON at
        // every ingress) anchors the ML-DSA key a turn carries in the AGENT
        // CELL's own `pq_identity`. A genesis cell without one is a cell that
        // cannot act: every turn it is the agent of is refused
        // `pq-identity-not-enrolled` — which, for the faucet cell, means every
        // faucet grant dies at finalization after the endpoint said `success`.
        // The key is NOT reconstructible from the published ed25519 pubkey (it
        // derives from the SEED), so genesis publishes it and this is where it
        // is committed. Absent field ⇒ classical-only cell, exactly as before.
        let ledger_cell = match cell["ml_dsa_public_key"].as_str() {
            Some(ml_dsa_hex) => {
                let Some(ml_dsa_public_key) = hex_decode_vec(ml_dsa_hex) else {
                    tracing::warn!(cell = %label, "skipping genesis cell with malformed ml_dsa_public_key");
                    stats.invalid += 1;
                    continue;
                };
                match dregg_cell::Cell::with_hybrid_balance(
                    public_key,
                    &ml_dsa_public_key,
                    token_id,
                    initial_balance,
                ) {
                    Ok(cell) => cell,
                    Err(error) => {
                        tracing::warn!(
                            cell = %label,
                            %error,
                            "skipping genesis cell whose ml_dsa_public_key is not a canonical ML-DSA-65 key"
                        );
                        stats.invalid += 1;
                        continue;
                    }
                }
            }
            None => dregg_cell::Cell::with_balance(public_key, token_id, initial_balance),
        };
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

/// `true` iff this store has never checkpointed AND has never committed a finalized
/// turn — i.e. the ledger in hand right now is, by construction, the pre-turn boot
/// baseline and not a partial recovery. The two conditions together are what keep
/// [`complete_boot_recovery`]'s height-0 checkpoint from ever overwriting a real one
/// or laundering a short reconstruction into the store.
fn is_prefinalization_boot(store: &dregg_persist::PersistentStore) -> bool {
    matches!(store.load_latest_ledger_checkpoint(), Ok(None))
        && matches!(store.commit_cursor(), Ok(0))
}

/// Whether the caller has materialized the WHOLE boot-time ledger baseline before
/// calling [`complete_boot_recovery`], and may therefore pin it as the height-0
/// checkpoint every later restart reconstructs from.
#[derive(Clone, Copy, PartialEq, Eq)]
enum BootBaseline {
    /// `run_node`: genesis `initial_cells`, the starbridge factory cells and the
    /// demo execution-lease cells are all in the ledger by the time it calls.
    Complete,
    /// `run_mcp`: it builds none of the boot seeds, so its ledger is genesis ⊕
    /// overlay only. Checkpointing THAT would freeze a short baseline into the
    /// store and brick every later `run_node` on the same data dir — the exact
    /// failure this function exists to end, written by the fix for it.
    ///
    /// ⚠ NAMED RESIDUAL, not closed here: `run_mcp` and `run_node` build
    /// DIFFERENT boot baselines, and both commit turns. A data dir driven by
    /// `mcp` alone is self-consistent (it records roots over the baseline it
    /// builds) and a data dir driven by `run` alone is self-consistent; a dir
    /// driven by BOTH is not, and the second one to boot fail-closes on
    /// convergence. That predates this function — `run_mcp` never seeded
    /// starbridge — and what changed is only that the divergence is now
    /// REFUSED on both paths instead of served on one. The real fix is one
    /// boot-baseline builder both entrypoints share.
    PartialServeOnly,
}

/// **THE BOOT-RECOVERY WELD — the one named step every serving entrypoint runs.**
///
/// `NodeState::new*` deliberately leaves the ledger at `checkpoint ⊕ commit-log
/// overlay` and renders NO integrity verdict. On a node below its first ledger
/// checkpoint that is only the touched-cell delta on an empty base, while every
/// commit record's `ledger_root` commits the FULL ledger (genesis ⊕ touched) — so
/// comparing there would fail-close every legitimate sub-checkpoint restart. That
/// is why the verdict is deferred (see [`crate::state::NodeState::verify_recovery_convergence`]
/// and `run_boot_torn_tail_recovery`).
///
/// ⚑ A DEFERRED CHECK IS A CHECK THAT SOMEBODY MUST STILL RUN, and for four days
/// exactly one caller did. Before the deferral landed (`e5c92ac80`, 2026-07-26) the
/// early `recover_to_last_consistent` fatal fired inside the CONSTRUCTOR, so it
/// covered `run_node` and `run_mcp` alike. After it, the verdict lived only in
/// `run_node`'s body — and `run_mcp` (which unlocks the cipherclerk and serves
/// turn-COMMITTING tools over stdio) constructed a `NodeState` on the same data dir,
/// never reseeded the genesis baseline, never verified convergence, and served. A
/// store whose recorded finalized root the ledger does not reconstruct was accepted
/// there in silence. The commit that moved the verdict said "it does not remove a
/// gate"; that was true of `run_node` and false of the process next to it.
///
/// So the two steps are welded into one function with one name, and both
/// entrypoints call it:
///
/// 1. **Rebuild the full finalized ledger** — [`reseed_genesis_then_overlay`], which
///    lifts the recovered overlay out, materializes the genesis baseline on a FRESH
///    ledger (so `genesis_moves` replay EXACTLY ONCE), re-applies the overlay
///    last-writer-wins, and re-applies post-checkpoint removals. It is IDEMPOTENT by
///    construction, which is what lets `run_node` keep its own earlier reseed (it
///    needs the materialized wells before this point) and still route through here.
/// 2. **Render the verdict** — `verify_recovery_convergence`, carrying the
///    crash-consistency, quorum-signed-anchor and anti-rollback legs.
///
/// 3. **Pin the boot baseline as a height-0 ledger checkpoint** — see
///    [`BootBaseline`]. This is what makes step 2 survivable on a young node at all
///    (below), and only a caller that actually built the whole baseline may do it.
///
/// FAIL CLOSED: `Err` means refuse to serve. A node with no `genesis.json` skips
/// step 1 (there is no baseline to rebuild) and STILL runs step 2.
///
/// ⚑ MEASURED 2026-07-30 against the real binary (issue #59). A fresh solo node,
/// three faucet grants, `kill -9`, restart:
///
/// ```text
/// recovery convergence failed: reconstructed ledger root 26298416… does not match
/// the durably recorded finalized root 1f9ba1aa… (STORE INTEGRITY EVENT)
/// ```
///
/// on its own healthy, never-tampered image — after `e5c92ac80` had already fixed
/// the earlier, louder refusal one step upstream. The image was fine. The
/// reconstruction was short by exactly the **ten starbridge factory cells**
/// (`starbridge_seed`) plus the demo execution-lease cells: the boot baseline is
/// `initial_cells ⊕ starbridge ⊕ demo-lease`, but only `initial_cells` is
/// reconstructible from `genesis.json`, and a cell that no finalized turn ever
/// TOUCHED is in no commit-log overlay either. Below the first ledger checkpoint
/// there was nothing carrying them, so every record's full-ledger root was
/// unreachable — exactly the reporter's "`LEDGER_CHECKPOINT_INTERVAL` must not
/// define the earliest survivable restart", one layer under where they found it.
///
/// The seeder even reports `existing=10` on that restart, because
/// `starbridge_seed::seed_one_cell` accepts a **marker file** as evidence a cell is
/// present. Two authorities for one fact; the ledger is the one that counts.
async fn complete_boot_recovery(
    node_state: &state::NodeState,
    data_path: &std::path::Path,
    baseline: BootBaseline,
) -> Result<(), String> {
    let genesis_path = data_path.join("genesis.json");
    if genesis_path.exists() {
        match std::fs::read_to_string(&genesis_path)
            .map_err(|e| e.to_string())
            .and_then(|text| {
                serde_json::from_str::<serde_json::Value>(&text).map_err(|e| e.to_string())
            }) {
            Ok(genesis) => {
                let mut s = node_state.write().await;
                let removed_since_checkpoint = {
                    let cp_h = s.store.latest_ledger_checkpoint_height().unwrap_or(0);
                    s.store.removed_cell_ids_since(cp_h).unwrap_or_default()
                };
                let _ =
                    reseed_genesis_then_overlay(&genesis, &mut s.ledger, &removed_since_checkpoint);
            }
            Err(e) => {
                // Not fatal by itself — but say it, because the verdict below is now
                // being taken against a ledger with no genesis baseline under it and
                // will (correctly) refuse a node that has finalized turns.
                tracing::warn!(
                    error = %e,
                    path = %genesis_path.display(),
                    "genesis.json is present but unreadable/unparseable — the recovery \
                     verdict runs WITHOUT a rebuilt genesis baseline"
                );
            }
        }
    }
    node_state.verify_recovery_convergence().await?;

    // ── PIN THE BASELINE ────────────────────────────────────────────────────
    // A node that has never checkpointed and has never committed a finalized turn
    // is standing on the complete boot baseline RIGHT NOW and will never be able to
    // rebuild it from `genesis.json` alone. Write it as the height-0 checkpoint, so
    // the very first crash — before turn 1, before block 100, before anything — has
    // a full-ledger snapshot to recover onto.
    //
    // The conditions are what keep this from being a way to launder a short ledger
    // into the store: NO existing checkpoint (never overwrite a real one) and a ZERO
    // commit cursor (nothing finalized yet, so this ledger is by construction the
    // pre-turn baseline and not a partial recovery). `PartialServeOnly` callers are
    // excluded outright.
    if baseline == BootBaseline::Complete {
        let s = node_state.read().await;
        if is_prefinalization_boot(&s.store) {
            match s.store.checkpoint_ledger(&s.ledger, 0) {
                Ok(()) => info!(
                    cells = s.ledger.len(),
                    "pinned the boot ledger baseline as the height-0 checkpoint — a crash \
                     before the first periodic checkpoint is now recoverable"
                ),
                Err(e) => {
                    // Fail closed. Without this checkpoint the node is one `kill -9`
                    // away from an image it cannot reconstruct, and saying so at boot
                    // is the whole point of writing it here.
                    return Err(format!(
                        "could not pin the boot ledger baseline as the height-0 checkpoint \
                         ({e}) — refusing to serve a node whose first crash would be \
                         unrecoverable"
                    ));
                }
            }
        }
    }
    Ok(())
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
    removed_since_checkpoint: &[dregg_cell::CellId],
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

    // 4. Re-apply the post-checkpoint REMOVALS (MakeSovereign tombstones): the
    //    fresh genesis baseline re-materialized every genesis cell, so a genesis
    //    cell removed after the checkpoint must be deleted AGAIN — the surviving
    //    overlay (step 1/3) carries only cells that still exist, never the erasure.
    //    Without this the reconstructed root diverges and `verify_recovery_
    //    convergence` fails closed on a genesis-cell-made-sovereign restart.
    for id in removed_since_checkpoint {
        let _ = ledger.remove(id);
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
    // Collect the published ML-DSA-65 keys alongside the ed25519 keys: the
    // federation_id commits to the HYBRID roster (genesis.rs derives it with
    // `derive_federation_id_hybrid_with_epoch`, and boot re-derives the same way via
    // `set_federation_keys_hybrid`). Re-deriving here over ed25519 keys ALONE
    // computed a different id, so a well-formed current-binary descriptor failed its
    // own tamper check and cross-federation registration could never succeed. A
    // legacy descriptor missing any ML-DSA key falls back to the ed25519-only
    // projection (mirrors the boot-time `ml_dsa_complete` handling).
    let mut ml_dsa_keys: Vec<dregg_federation::frost::MlDsaPublicKey> =
        Vec::with_capacity(validators.len());
    let mut ml_dsa_complete = true;
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
        match v["ml_dsa_public_key"]
            .as_str()
            .and_then(parse_ml_dsa_public_key)
        {
            Some(k) => ml_dsa_keys.push(k),
            None => ml_dsa_complete = false,
        }
    }
    if pubkeys.is_empty() {
        eprintln!("error: descriptor has zero validators");
        std::process::exit(1);
    }
    let ml_dsa_keys = if ml_dsa_complete {
        ml_dsa_keys
    } else {
        Vec::new()
    };

    // Recompute the federation_id and reject a tampered descriptor. This MUST use the
    // same projection genesis committed to, or the fail-closed check fires on honest
    // descriptors (which is what it did).
    let derived = dregg_federation::derive_federation_id_hybrid_with_epoch(
        &pubkeys,
        &ml_dsa_keys,
        committee_epoch,
    );
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

/// Outcome of installing the Lean-verified ML-DSA verify core as `dregg_pq::ml_dsa_verify`'s authority.
/// Re-exported from `dregg-pq` (the single, shared install object every deployed process routes through);
/// node keeps the name for back-compat with `tests/mldsa_live_verify.rs` and `tests/mldsa_live_sign.rs`.
pub use dregg_pq::MlDsaVerifyCoreInstall;

/// Announce that a verified PQ core is ABSENT, so this process's `site` direction will be answered
/// by the UNAUDITED `fips204`/`ml-kem` crate under `dregg-pq`'s DECLARED bypass.
///
/// ⚑ WHY THIS REPLACED SIX BARE `warn!`s (twin#13). Each install arm used to log its own
/// warn-and-continue and stop there, which under-described the state three ways: it did not say that
/// reaching the crate at all requires the operator's `DREGG_ALLOW_UNAUDITED_PQ=1` (without it
/// `dregg-pq` ABORTS the process on the first such operation — the fallback is not silent), it did
/// not say that `DREGG_REQUIRE_LEAN=1` now REVOKES that bypass, and it named no way to observe
/// whether the crate ever actually answered. A boot line is a statement about EXPORTS; the live
/// question is which implementation answered a given operation, and that is
/// `dregg_pq_unaudited_crate_answers_total{site="…"}` (see `metrics::publish_pq_provenance`).
///
/// The ACCEPT/REJECT gate is logged at `error!`, the other five at `warn!`. That asymmetry is the
/// point of `PqSite::is_accept_reject_gate`: `ml_dsa_verify` is the one direction whose answer is a
/// security VERDICT, so an absent core there moves the accept/reject authority for ~10 surfaces onto
/// a third-party crate. A keygen has no verdict to fail open on — it needs visibility, not an alarm.
fn announce_unverified_pq_site(site: dregg_pq::PqSite, detail: &str) {
    let common = format!(
        "The `{label}` direction is answered by the UNAUDITED crate primitive ONLY under \
         dregg-pq's DECLARED bypass: {allow}=1 must be set, or the process ABORTS (uncatchably) on \
         the first such operation. `{require}=1` REVOKES that bypass. WATCH \
         dregg_pq_unaudited_crate_answers_total{{site=\"{label}\"}} — a non-zero value means the \
         unaudited crate answered this direction in this process, which one boot log line cannot \
         tell you. Rebuild against a HEAD-matching archive containing all six PQ exports.",
        label = site.label(),
        allow = dregg_pq::ALLOW_UNAUDITED_PQ_ENV,
        require = dregg_pq::REQUIRE_LEAN_ENV,
    );
    if site.is_accept_reject_gate() {
        error!(
            site = site.label(),
            "UNVERIFIED PQ ACCEPT/REJECT GATE: {detail} This is the one PQ direction whose answer \
             is a SECURITY VERDICT — with no verified core the accept/reject authority behind \
             token/revocation, the lightclient, cell-crypto, the wire, turn/authorize, captp and \
             blocklace/pq is a third-party crate. {common}"
        );
    } else {
        warn!(site = site.label(), "UNVERIFIED PQ: {detail} {common}");
    }
}

/// Install the extracted, Lean-verified REAL, full-byte ML-DSA verify core (`MlDsaVerifyReal.verifyCore`,
/// BRICK 8) as the accept/reject AUTHORITY behind `dregg_pq::ml_dsa_verify` — taking the `fips204` crate
/// OUT of the node's verify TCB. Thin node-side wrapper over the SHARED
/// `dregg_pq::install_verified_mldsa_verify_core` (the one tested install that node + the SDK-hosted wire
/// silo + starbridge-v2 all route through): it injects the two `dregg-lean-ffi` archive symbols. Gated on
/// `fips204_verify_real_core_available()` so a stale archive that lacks the export does not brick
/// verification (an absent core would make `ml_dsa_verify` fail closed on every call). Idempotent and
/// once-per-process. Exercised directly by `tests/mldsa_live_verify.rs`, so the running-binary gate drives
/// the EXACT production install.
pub fn install_mldsa_verified_verify_core() -> MlDsaVerifyCoreInstall {
    dregg_pq::install_verified_mldsa_verify_core(
        dregg_lean_ffi::fips204_verify_real_core_available,
        |w| dregg_lean_ffi::shadow_fips204_verify_real(w).ok(),
    )
}

/// Outcome of installing the extracted Lean-verified ML-DSA SIGN core behind `dregg_pq::ml_dsa_sign_core`.
///
/// ⚠ HONEST SCOPE — this is deliberately NOT the sign-side twin of [`MlDsaVerifyCoreInstall`]. The verify
/// install wires BRICK 8's FULL-BYTE `MlDsaVerifyReal.verifyCore` as the authority behind the DEPLOYED
/// byte-level `dregg_pq::ml_dsa_verify`. The sign core available today is only the SCALAR (n=1)
/// `Fips204Verify.signCore` (a 5-int→3-int Fiat–Shamir-with-aborts object). Installing it makes that
/// verified scalar object the backend of `dregg_pq::ml_dsa_sign_core` (the scalar-model seam) — it does NOT
/// route the deployed `MlDsaKey::sign` byte-level signer, which STILL calls the `fips204` crate. So a
/// successful install here does NOT take the crate out of the node's SIGN TCB; the real full-byte sign core
/// (the same 8-brick build the verify side got, adding MakeHint + the rejection loop) is the named
/// follow-up.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MlDsaSignCoreInstall {
    /// The scalar sign core was installed by THIS call (now the backend of `ml_dsa_sign_core`).
    Installed,
    /// A sign core was already installed this process (install is once-per-process).
    AlreadyInstalled,
    /// The linked Lean archive does not export `dregg_fips204_sign`; no sign core installed, and
    /// `ml_dsa_sign_core` returns `None` (callers use the `fips204` crate).
    ExportAbsent,
}

/// Install the extracted, Lean-verified SCALAR ML-DSA sign core (`Fips204Verify.signCore`) as the backend
/// of `dregg_pq::ml_dsa_sign_core`. See [`MlDsaSignCoreInstall`] for the honest scope: this wires the n=1
/// scalar model, NOT the deployed byte-level `MlDsaKey::sign`, so the `fips204` crate is NOT removed from
/// the node's SIGN TCB by this call. Gated on `fips204_sign_core_available()` so a stale archive without the
/// export is reported (rather than leaving `ml_dsa_sign_core` silently returning `None`). Idempotent,
/// once-per-process. Called from the node startup path AND exercised directly by `tests/mldsa_live_sign.rs`,
/// so the running-binary gate drives the EXACT production install.
pub fn install_mldsa_verified_sign_core() -> MlDsaSignCoreInstall {
    if !dregg_lean_ffi::fips204_sign_core_available() {
        return MlDsaSignCoreInstall::ExportAbsent;
    }
    if dregg_pq::install_lean_sign_core(|w| dregg_lean_ffi::shadow_fips204_sign(w).ok()) {
        MlDsaSignCoreInstall::Installed
    } else {
        MlDsaSignCoreInstall::AlreadyInstalled
    }
}

/// Outcome of installing the Lean-verified REAL, full-byte ML-DSA sign core as the PRODUCER behind the
/// deployed `dregg_pq::MlDsaKey::sign` / `ml_dsa_sign_from_seed`. Re-exported from `dregg-pq` (the single
/// shared install object); node keeps the name for the running-binary gate `tests/mldsa_live_sign.rs`.
pub use dregg_pq::MlDsaSignCoreRealInstall;

/// Install the extracted, Lean-verified REAL, full-byte ML-DSA-65 sign core
/// (`Dregg2.Crypto.MlDsaSignReal.signCore`, the brick-8 SIGN analog) as the PRODUCER behind the DEPLOYED
/// byte-level signer `dregg_pq::MlDsaKey::sign` — taking the `fips204` crate OUT of the node's SIGN TCB.
/// Thin node-side wrapper over the SHARED `dregg_pq::install_verified_mldsa_sign_core_real`: it injects the
/// two `dregg-lean-ffi` archive symbols. Gated on `fips204_sign_real_core_available()` so a stale archive
/// that lacks the export does not brick signing (an absent core would make `try_sign` fail closed on every
/// call). Idempotent and once-per-process. Exercised directly by `tests/mldsa_live_sign.rs`, so the
/// running-binary gate drives the EXACT production install.
///
/// ⚠ On the installed path the deployed signer is DETERMINISTIC (`rnd = 0`, the FIPS 204 deterministic
/// signing variant — spec-valid); the crate fallback path is hedged/randomized.
pub fn install_mldsa_verified_sign_core_real() -> MlDsaSignCoreRealInstall {
    dregg_pq::install_verified_mldsa_sign_core_real(
        dregg_lean_ffi::fips204_sign_real_core_available,
        |w| dregg_lean_ffi::shadow_fips204_sign_real(w).ok(),
    )
}

/// Outcome of installing the Lean-verified REAL ML-DSA keygen core behind identity-key derivation.
pub use dregg_pq::MlDsaKeygenCoreRealInstall;

/// Install the extracted, KAT-anchored full-byte ML-DSA-65 keygen core as the authority behind
/// `MlDsaKey::from_ed25519_seed`. The shared dregg-pq seam keeps archive linking out of the light leaf.
pub fn install_mldsa_verified_keygen_core_real() -> MlDsaKeygenCoreRealInstall {
    dregg_pq::install_verified_mldsa_keygen_core_real(
        dregg_lean_ffi::mldsa_keygen_real_core_available,
        |w| dregg_lean_ffi::shadow_mldsa_keygen_real(w).ok(),
    )
}

/// Outcome of installing the Lean-verified REAL ML-KEM decaps core as `dregg_pq::HybridResponder::finish`'s
/// authority. Re-exported from `dregg-pq` (the single shared install object); node keeps the name for the
/// running-binary gate `tests/mlkem_live_decaps.rs`.
pub use dregg_pq::MlKemDecapsCoreInstall;

/// Install the extracted, Lean-verified REAL, full-byte ML-KEM-768 decaps core
/// (`Dregg2.Crypto.MlKemDecaps.mlkemDecaps`, BRICK K6) as the shared-secret AUTHORITY behind
/// `dregg_pq::HybridResponder::finish` — taking the `ml-kem` crate OUT of the node's KEM-decaps TCB. Thin
/// node-side wrapper over the SHARED `dregg_pq::install_verified_mlkem_decaps_core`: it injects the two
/// `dregg-lean-ffi` archive symbols. Gated on `mlkem_decaps_real_core_available()` so a stale archive that
/// lacks the export does not brick decaps (an absent core would make `finish` fail closed on every ciphertext).
/// Idempotent and once-per-process. Exercised directly by `tests/mlkem_live_decaps.rs`, so the running-binary
/// gate drives the EXACT production install.
pub fn install_mlkem_verified_decaps_core() -> MlKemDecapsCoreInstall {
    dregg_pq::install_verified_mlkem_decaps_core(
        dregg_lean_ffi::mlkem_decaps_real_core_available,
        |w| dregg_lean_ffi::shadow_mlkem_decaps_real(w).ok(),
    )
}

/// Outcome of installing the Lean-verified REAL ML-KEM encaps core as `dregg_pq::hybrid_kem::initiate`'s
/// authority. Re-exported from `dregg-pq` (the single shared install object); node keeps the name for the
/// running-binary gate `tests/mlkem_live_encaps.rs`.
pub use dregg_pq::MlKemEncapsCoreInstall;

/// Install the extracted, Lean-verified REAL, full-byte ML-KEM-768 encaps core
/// (`Dregg2.Crypto.MlKemEncaps.mlkemEncaps`, BRICK K5) as the ciphertext+secret AUTHORITY behind
/// `dregg_pq::hybrid_kem::initiate` — taking the `ml-kem` crate OUT of the node's KEM-encaps TCB. Thin
/// node-side wrapper over the SHARED `dregg_pq::install_verified_mlkem_encaps_core`: it injects the two
/// `dregg-lean-ffi` archive symbols. Gated on `mlkem_encaps_real_core_available()` so a stale archive that
/// lacks the export does not brick encaps (an absent core would make `initiate` fail on every offer).
/// Idempotent and once-per-process. Exercised directly by `tests/mlkem_live_encaps.rs`, so the running-binary
/// gate drives the EXACT production install.
pub fn install_mlkem_verified_encaps_core() -> MlKemEncapsCoreInstall {
    dregg_pq::install_verified_mlkem_encaps_core(
        dregg_lean_ffi::mlkem_encaps_real_core_available,
        |w| dregg_lean_ffi::shadow_mlkem_encaps_real(w).ok(),
    )
}

/// Outcome of installing the Lean-verified REAL ML-KEM keygen core behind responder/bare key generation.
pub use dregg_pq::MlKemKeygenCoreInstall;

/// Install the extracted, KAT-anchored full-byte ML-KEM-768 keygen core as the authority behind both
/// `hybrid_kem::responder_offer` and `ml_kem768_keygen`.
pub fn install_mlkem_verified_keygen_core() -> MlKemKeygenCoreInstall {
    dregg_pq::install_verified_mlkem_keygen_core(
        dregg_lean_ffi::mlkem_keygen_real_core_available,
        |w| dregg_lean_ffi::shadow_mlkem_keygen_real(w).ok(),
    )
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
mod boot_recovery_baseline_tests {
    use super::*;
    use dregg_cell::Ledger;

    fn cell(seed: u8, balance: i64) -> dregg_cell::Cell {
        dregg_cell::Cell::with_balance([seed; 32], [7u8; 32], balance)
    }

    /// A store holding ONE finalized turn whose recorded root commits
    /// `boot_baseline ⊕ touched`, where `boot_baseline` contains a cell that is
    /// NOT in any `genesis.json` — the starbridge/demo-lease shape. Returns the
    /// full ledger so a caller can checkpoint it.
    fn store_with_one_turn_over_an_unreconstructible_baseline(
        dir: &std::path::Path,
    ) -> (dregg_persist::PersistentStore, Ledger) {
        let store = dregg_persist::PersistentStore::open(&dir.join("dregg.redb")).expect("open");
        let mut ledger = Ledger::new();
        // The BOOT SEED: born at boot from a descriptor, never named by
        // genesis.json, and never touched by a finalized turn. Nothing but a
        // checkpoint can carry it across a restart.
        ledger
            .insert_cell(cell(0xbb, 1_000))
            .expect("boot-seeded cell");
        // A cell a finalized turn touches — this one IS in the commit-log overlay.
        let touched = cell(0x11, 42);
        ledger.insert_cell(touched.clone()).expect("touched cell");
        let record = dregg_persist::CommitRecord {
            ordinal: 0,
            height: 1,
            block_id: [0u8; 32],
            block_executed_up_to: 0,
            turn_hash: [0xc1; 32],
            creator: [0u8; 32],
            receipt_hash: [0xd1; 32],
            ledger_root: crate::blocklace_sync::canonical_ledger_root(&ledger),
            touched_cells: vec![touched],
            removed: Vec::new(),
        };
        store.commit_finalized_turn(0, &record).expect("commit");
        (store, ledger)
    }

    /// POLE 1 — THE WOUND (issue #59, measured against the real binary
    /// 2026-07-30). With no ledger checkpoint, a cell that entered the ledger at
    /// BOOT (not from `genesis.json`) and was never TOUCHED by a finalized turn is
    /// carried by nothing: not the checkpoint (there is none), not the commit-log
    /// overlay (only touched cells). The reconstruction is short by exactly that
    /// cell, the canonical root does not match the recorded finalized root, and
    /// the node refuses its own healthy image.
    ///
    /// This test asserts the REFUSAL, deliberately. It is the pre-state pole 2
    /// must beat, and if it ever stops refusing this test stops being about
    /// anything.
    #[tokio::test]
    async fn boot_seeded_cell_is_unreconstructible_without_a_checkpoint() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let (store, _full) = store_with_one_turn_over_an_unreconstructible_baseline(tmp.path());
        assert!(
            store
                .load_latest_ledger_checkpoint()
                .expect("read")
                .is_none(),
            "the window this is about is DEFINED by having no checkpoint"
        );
        drop(store);

        let state = state::NodeState::new(tmp.path(), vec![]).expect("construct");
        // No genesis.json in this dir, so `complete_boot_recovery` reseeds nothing
        // and verifies what the overlay alone rebuilt.
        let err = complete_boot_recovery(&state, tmp.path(), BootBaseline::Complete)
            .await
            .expect_err(
                "a ledger short of a boot-seeded cell must NOT be accepted — if this passes, \
                 the convergence verdict has stopped comparing anything",
            );
        assert!(
            err.contains("convergence"),
            "the refusal must name the convergence failure; got: {err}"
        );
    }

    /// POLE 2 — THE FIX. The SAME image, with the boot baseline pinned as a
    /// height-0 ledger checkpoint before the crash. `NodeState::new` restores
    /// `checkpoint ⊕ overlay`, which IS the full finalized ledger, and the verdict
    /// converges. This is what `complete_boot_recovery` writes on a fresh node's
    /// first boot.
    #[tokio::test]
    async fn the_height_zero_boot_checkpoint_makes_that_same_image_recoverable() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let (store, full) = store_with_one_turn_over_an_unreconstructible_baseline(tmp.path());
        store
            .checkpoint_ledger(&full, 0)
            .expect("pin the boot baseline");
        drop(store);

        let state = state::NodeState::new(tmp.path(), vec![]).expect("construct");
        complete_boot_recovery(&state, tmp.path(), BootBaseline::Complete)
            .await
            .expect("the pinned boot baseline must make this image recoverable");
    }

    /// POLE 3 — the checkpoint must not become a way to accept ANYTHING. Same
    /// shape as pole 2, but the recorded finalized root is one the ledger does not
    /// reconstruct to. A checkpoint is present, so pole 2's mechanism is fully in
    /// play; the verdict must still refuse.
    #[tokio::test]
    async fn a_checkpointed_but_divergent_image_is_still_refused() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let store =
            dregg_persist::PersistentStore::open(&tmp.path().join("dregg.redb")).expect("open");
        let mut ledger = Ledger::new();
        ledger
            .insert_cell(cell(0xbb, 1_000))
            .expect("boot-seeded cell");
        let touched = cell(0x11, 42);
        ledger.insert_cell(touched.clone()).expect("touched cell");
        let record = dregg_persist::CommitRecord {
            ordinal: 0,
            height: 1,
            block_id: [0u8; 32],
            block_executed_up_to: 0,
            turn_hash: [0xc1; 32],
            creator: [0u8; 32],
            receipt_hash: [0xd1; 32],
            ledger_root: [0xde; 32], // deliberately NOT the post-overlay root
            touched_cells: vec![touched],
            removed: Vec::new(),
        };
        store.commit_finalized_turn(0, &record).expect("commit");
        store.checkpoint_ledger(&ledger, 0).expect("checkpoint");
        drop(store);

        let state = state::NodeState::new(tmp.path(), vec![]).expect("construct");
        let err = complete_boot_recovery(&state, tmp.path(), BootBaseline::Complete)
            .await
            .expect_err("a divergent image must fail closed even with a checkpoint present");
        assert!(
            err.contains("convergence"),
            "the refusal must name the convergence failure; got: {err}"
        );
    }

    /// The guard on WHEN the boot baseline may be pinned. Both conditions are
    /// load-bearing: an existing checkpoint means this ledger is a RECOVERY (and
    /// may legitimately be mid-reconstruction), and a non-zero commit cursor means
    /// turns have been finalized (so this ledger is no longer the pre-turn
    /// baseline). Either one alone would let a short reconstruction be frozen into
    /// the store as if it were the baseline.
    #[tokio::test]
    async fn the_baseline_pin_refuses_a_store_that_is_not_a_fresh_boot() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let store =
            dregg_persist::PersistentStore::open(&tmp.path().join("dregg.redb")).expect("open");
        assert!(
            is_prefinalization_boot(&store),
            "a store with no checkpoint and no finalized turn IS a fresh boot"
        );

        std::fs::create_dir_all(tmp.path().join("b")).expect("subdir");
        let (store2, full) =
            store_with_one_turn_over_an_unreconstructible_baseline(&tmp.path().join("b"));
        assert!(
            !is_prefinalization_boot(&store2),
            "a NON-ZERO commit cursor means turns are finalized — this ledger is no longer the \
             pre-turn baseline and pinning it would freeze a partial recovery"
        );
        store2.checkpoint_ledger(&full, 0).expect("checkpoint");
        assert!(
            !is_prefinalization_boot(&store2),
            "an EXISTING checkpoint must never be overwritten by the boot pin"
        );
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
