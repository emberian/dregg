//! `dregg-client-sign` — the SDK-side reference CLIENT-SIGN tool.
//!
//! One small binary that lets any subprocess-capable harness commit a REAL
//! client-signed turn to a dregg node without linking the SDK itself: load a
//! named `~/.dregg/profiles/` identity, build a single-action `EmitEvent`
//! turn carrying an opaque payload, hybrid-sign it (Ed25519 + ML-DSA-65 over
//! the same turn bytes — the deployed `require_pq` posture), and POST the
//! postcard `SignedTurn` to the node's client-signed ingress `/turns/submit`.
//!
//! Why a bin HERE and not a `dregg turn` verb: the CLI crate is deliberately
//! SDK-free ("Lean-free and cross-platform clean", cli/Cargo.toml) and its own
//! turn module documents that the signed-envelope path belongs to the SDK.
//! `dregg-sdk-net` IS the networked SDK layer — every dependency this tool
//! needs is already in the crate's graph, so the whole surface is this file.
//!
//! Verbs (stdout = exactly one JSON object; progress on stderr):
//!
//!   join   ensure the profile exists (create on first use) and its canonical
//!          agent cell is faucet-materialized on the node — no turn.
//!   send   commit ONE client-signed turn AS the profile's own cell: an
//!          `EmitEvent` on the cell (topic = `symbol(--topic)`, data = the
//!          payload packed 8 bytes/word into the u64-safe low lane) with the
//!          full payload string as the turn memo (length-prefixed into
//!          `Turn::hash`, so the signature binds it). Exit 0 only when the
//!          node has receipted the turn.
//!
//! Env (flags win): DREGG_NODE_URL (default http://127.0.0.1:8899),
//! DREGG_API_TOKEN (bearer for the protected ingress) or DREGG_NODE_PASSPHRASE
//! (unlock fallback), DREGG_PROFILE / the profiles `ACTIVE` file (the SDK's
//! own active-profile convention) when `--profile` is not given.

use dregg_sdk::AgentCipherclerk;
use dregg_sdk::profiles;
use dregg_sdk_net::NodeHttpClient;
use dregg_turn::action::{Effect, Event, symbol};
use dregg_turn::{ComputronCosts, Turn, TurnExecutor};

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

fn err(msg: String) -> Box<dyn std::error::Error> {
    msg.into()
}

/// The low-lane payload packing: 8 bytes per 32-byte word, in `word[24..32]`.
/// A value confined to the low 8 bytes is a valid element of ANY field the
/// executors interpret words in (< 2^64), the same discipline the node's
/// Lean-authoritative state projection enforces for `SetField` lanes.
const LANE_LO: usize = 24;
const LANE_BYTES: usize = 8;

fn pack_payload(payload: &[u8]) -> Vec<[u8; 32]> {
    payload
        .chunks(LANE_BYTES)
        .map(|chunk| {
            let mut word = [0u8; 32];
            word[LANE_LO..LANE_LO + chunk.len()].copy_from_slice(chunk);
            word
        })
        .collect()
}

fn env(name: &str) -> Option<String> {
    std::env::var(name).ok().filter(|v| !v.is_empty())
}

fn node_url_default() -> String {
    env("DREGG_NODE_URL").unwrap_or_else(|| "http://127.0.0.1:8899".to_string())
}

async fn get_json(http: &reqwest::Client, url: &str) -> Result<serde_json::Value> {
    let resp = http
        .get(url)
        .send()
        .await
        .map_err(|e| err(format!("GET {url}: {e}")))?;
    let status = resp.status();
    if !status.is_success() {
        return Err(err(format!("GET {url} returned {status}")));
    }
    resp.json()
        .await
        .map_err(|e| err(format!("parse {url}: {e}")))
}

/// The bearer for the node's protected write surface: `--token` /
/// `DREGG_API_TOKEN` directly, else unlock with `DREGG_NODE_PASSPHRASE`
/// (`POST /api/cipherclerk/unlock` — never a blind `.json()`: the node's
/// rate-limited 429 carries an empty body).
async fn ensure_token(
    http: &reqwest::Client,
    node_url: &str,
    token_flag: Option<String>,
) -> Result<String> {
    if let Some(t) = token_flag.or_else(|| env("DREGG_API_TOKEN")) {
        return Ok(t);
    }
    let passphrase = env("DREGG_NODE_PASSPHRASE").ok_or_else(|| {
        err("the node's /turns/submit is bearer-protected: set DREGG_API_TOKEN \
             (or --token), or DREGG_NODE_PASSPHRASE to unlock"
            .to_string())
    })?;
    let raw = http
        .post(format!("{node_url}/api/cipherclerk/unlock"))
        .json(&serde_json::json!({ "passphrase": passphrase }))
        .send()
        .await
        .map_err(|e| err(format!("POST /api/cipherclerk/unlock: {e}")))?;
    let status = raw.status();
    let body = raw
        .text()
        .await
        .map_err(|e| err(format!("read unlock response: {e}")))?;
    if !status.is_success() {
        return Err(err(format!("unlock returned {status}: {body}")));
    }
    let resp: serde_json::Value = serde_json::from_str(&body)
        .map_err(|e| err(format!("parse unlock response (HTTP {status}): {e}")))?;
    resp.get("bearer_token")
        .and_then(|t| t.as_str())
        .map(String::from)
        .ok_or_else(|| err(format!("unlock returned no bearer_token: {resp}")))
}

/// Materialize the profile's canonical cell on the node when absent
/// (`POST /api/faucet` with the public key — a turn cannot conjure its own
/// agent cell), then poll until visible. Idempotent.
async fn ensure_cell(
    http: &reqwest::Client,
    node_url: &str,
    cell_hex: &str,
    pk_hex: &str,
    fund: u64,
) -> Result<bool> {
    let cell_url = format!("{node_url}/api/cell/{cell_hex}");
    let found = |v: &serde_json::Value| v.get("found").and_then(|f| f.as_bool()) == Some(true);
    if found(&get_json(http, &cell_url).await?) {
        return Ok(false);
    }
    let resp: serde_json::Value = http
        .post(format!("{node_url}/api/faucet"))
        .json(&serde_json::json!({
            "recipient": cell_hex,
            "amount": fund,
            "public_key": pk_hex,
        }))
        .send()
        .await
        .map_err(|e| err(format!("POST /api/faucet: {e}")))?
        .json()
        .await
        .map_err(|e| err(format!("parse faucet response: {e}")))?;
    if resp.get("success").and_then(|s| s.as_bool()) != Some(true) {
        return Err(err(format!("faucet refused cell materialization: {resp}")));
    }
    eprintln!("[client-sign] faucet materialized cell (+{fund} computrons)");
    for _ in 0..40 {
        if found(&get_json(http, &cell_url).await?) {
            return Ok(true);
        }
        tokio::time::sleep(std::time::Duration::from_millis(250)).await;
    }
    Err(err(format!(
        "cell {cell_hex} not visible on the node 10s after faucet accept"
    )))
}

/// `--profile` flag → `DREGG_PROFILE` / `ACTIVE` (the SDK's own convention).
/// A SIGNER never guesses further: no profile configured is a hard error.
fn resolve_clerk(profile_flag: Option<&str>, create: bool) -> Result<(String, AgentCipherclerk)> {
    let name = match profile_flag {
        Some(p) => p.to_string(),
        None => profiles::active_name().ok_or_else(|| {
            err("no identity: pass --profile, or set DREGG_PROFILE / `dregg id use`".to_string())
        })?,
    };
    let exists = profiles::list()
        .map(|ps| ps.iter().any(|p| p.name == name))
        .unwrap_or(false);
    if !exists {
        if !create {
            return Err(err(format!(
                "profile '{name}' not found in {} — run `join` (or `dregg id create`) first",
                profiles::profiles_dir().display()
            )));
        }
        let info = profiles::create(&name).map_err(|e| err(format!("create profile '{name}': {e}")))?;
        eprintln!(
            "[client-sign] created identity '{name}' (pubkey {})",
            info.public_key_hex
        );
    }
    let clerk = profiles::load(&name).map_err(|e| err(format!("load profile '{name}': {e}")))?;
    Ok((name, clerk))
}

struct Flags {
    node_url: String,
    profile: Option<String>,
    token: Option<String>,
    topic: String,
    to: Option<String>,
    fund: u64,
    rest: Vec<String>,
}

fn parse_flags(argv: Vec<String>) -> Result<Flags> {
    let mut f = Flags {
        node_url: node_url_default(),
        profile: None,
        token: None,
        topic: "client-sign".to_string(),
        to: None,
        fund: 5000,
        rest: Vec::new(),
    };
    let mut it = argv.into_iter();
    while let Some(flag) = it.next() {
        let mut val = |name: &str| {
            it.next()
                .ok_or_else(|| err(format!("{name} requires a value")))
        };
        match flag.as_str() {
            "--node-url" => f.node_url = val("--node-url")?,
            "--profile" => f.profile = Some(val("--profile")?),
            "--token" => f.token = Some(val("--token")?),
            "--topic" => f.topic = val("--topic")?,
            "--to" => f.to = Some(val("--to")?),
            "--fund" => {
                f.fund = val("--fund")?
                    .parse()
                    .map_err(|e| err(format!("--fund must be a u64: {e}")))?
            }
            "--help" | "-h" => {
                eprintln!("{USAGE}");
                std::process::exit(0);
            }
            other => f.rest.push(other.to_string()),
        }
    }
    f.node_url = f.node_url.trim_end_matches('/').to_string();
    Ok(f)
}

const USAGE: &str = "dregg-client-sign: commit CLIENT-SIGNED turns to a dregg node as a named profile\n\n\
  join [--profile P] [--node-url U] [--fund N]\n\
       ensure the profile identity + its faucet-materialized cell (no turn)\n\
  send [--profile P] [--node-url U] [--token T] [--topic S] [--to CELL_HEX] PAYLOAD...\n\
       ONE hybrid-signed EmitEvent turn as the profile's own cell; payload\n\
       rides in the signed turn (memo + event data words)\n\n\
env (flags win): DREGG_NODE_URL, DREGG_API_TOKEN (or DREGG_NODE_PASSPHRASE\n\
to unlock), DREGG_PROFILE (the SDK's active-profile convention)";

async fn cmd_join(f: Flags) -> Result<()> {
    let http = reqwest::Client::new();
    let (name, clerk) = resolve_clerk(f.profile.as_deref(), true)?;
    let cell_hex = hex::encode(clerk.cell_id("default").as_bytes());
    let pk_hex = hex::encode(clerk.public_key().0);
    let materialized = ensure_cell(&http, &f.node_url, &cell_hex, &pk_hex, f.fund).await?;
    println!(
        "{}",
        serde_json::json!({
            "joined": true,
            "node": f.node_url,
            "profile": name,
            "public_key": pk_hex,
            "cell": cell_hex,
            "materialized": materialized,
        })
    );
    Ok(())
}

async fn cmd_send(f: Flags) -> Result<()> {
    if f.rest.is_empty() {
        return Err(err("send requires a payload".to_string()));
    }
    let payload = f.rest.join(" ");
    let http = reqwest::Client::new();
    let node = NodeHttpClient::new(&f.node_url);
    let (name, clerk) = resolve_clerk(f.profile.as_deref(), false)?;
    let cell = clerk.cell_id("default");
    let cell_hex = hex::encode(cell.as_bytes());

    // This tool SIGNS AS the profile — the only admissible target is the
    // profile's own cell (the node derives agent == the signer's cell).
    if let Some(to) = &f.to {
        if to.to_lowercase() != cell_hex {
            return Err(err(format!(
                "--to {to} is not profile '{name}'s own cell {cell_hex} — \
                 a client-signed turn can only act as the signer's cell"
            )));
        }
    }

    let bearer = ensure_token(&http, &f.node_url, f.token.clone()).await?;
    let cell_state = get_json(&http, &format!("{}/api/cell/{cell_hex}", f.node_url)).await?;
    if cell_state.get("found").and_then(|v| v.as_bool()) != Some(true) {
        return Err(err(format!(
            "cell {cell_hex} not on the node — run `dregg-client-sign join` first"
        )));
    }

    let federation_id = node
        .fetch_executor_federation_id()
        .await
        .map_err(|e| err(format!("fetch executor federation id: {e}")))?;
    let nonce = node
        .fetch_cell_nonce(&cell)
        .await
        .map_err(|e| err(format!("fetch own-cell nonce: {e}")))?;
    let chain_head = node
        .fetch_chain_head()
        .await
        .map_err(|e| err(format!("fetch chain head: {e}")))?;

    let effect = Effect::EmitEvent {
        cell,
        event: Event {
            topic: symbol(&f.topic),
            data: pack_payload(payload.as_bytes()),
        },
    };
    // Sign the action over the nonce the turn will CARRY (the on-ledger
    // nonce): the dregg-action-sig-v3 message binds the turn nonce, and
    // signing over anything local goes stale after the profile's first turn.
    let action = clerk.sign_action_hybrid(
        dregg_sdk::raw::unsigned_action_named(cell, &f.topic, vec![effect]),
        &federation_id,
        nonce,
    );
    let mut turn: Turn = clerk.make_turn_with_actions(vec![action]);
    turn.agent = cell;
    turn.nonce = nonce;
    turn.memo = Some(payload.clone());
    turn.valid_until = Some(i64::MAX / 2);
    turn.previous_receipt_hash = chain_head;
    turn.fee = TurnExecutor::new(ComputronCosts::default()).estimate_cost(&turn);

    let signed = clerk.sign_turn(&turn);
    let bytes =
        postcard::to_stdvec(&signed).map_err(|e| err(format!("serialize SignedTurn: {e}")))?;

    let resp = http
        .post(format!("{}/turns/submit", f.node_url))
        .header("Content-Type", "application/octet-stream")
        .header("Authorization", format!("Bearer {bearer}"))
        .body(bytes)
        .send()
        .await
        .map_err(|e| err(format!("POST /turns/submit: {e}")))?;
    let status = resp.status();
    if !status.is_success() {
        return Err(err(format!("/turns/submit returned {status}")));
    }
    let verdict: serde_json::Value = resp
        .json()
        .await
        .map_err(|e| err(format!("parse submit response: {e}")))?;
    if verdict.get("accepted").and_then(|a| a.as_bool()) != Some(true) {
        return Err(err(format!(
            "node refused the turn: {}",
            verdict
                .get("error")
                .and_then(|e| e.as_str())
                .unwrap_or("no reason given")
        )));
    }
    let turn_hash = verdict
        .get("turn_hash")
        .and_then(|h| h.as_str())
        .ok_or_else(|| err("accepted submit response missing turn_hash".to_string()))?
        .to_string();
    eprintln!("[client-sign] turn accepted: {turn_hash}; awaiting receipt...");

    // Receipt resolution across the consensus-finality window (~2s typical).
    // Fail-closed after 30s: exit 0 means RECEIPTED, never merely accepted.
    for _ in 0..120 {
        let receipts = get_json(&http, &format!("{}/api/receipts", f.node_url)).await?;
        if let Some(r) = receipts.as_array().and_then(|arr| {
            arr.iter()
                .find(|r| r.get("turn_hash").and_then(|t| t.as_str()) == Some(&turn_hash))
        }) {
            println!(
                "{}",
                serde_json::json!({
                    "sent": true,
                    "node": f.node_url,
                    "profile": name,
                    "agent_cell": cell_hex,
                    "to": cell_hex,
                    "topic": f.topic,
                    "payload": payload,
                    "turn_hash": turn_hash,
                    "receipt_hash": r.get("receipt_hash"),
                    "chain_index": r.get("chain_index"),
                    "finality": r.get("finality"),
                    "consensus_final": r.get("consensus_final"),
                })
            );
            return Ok(());
        }
        tokio::time::sleep(std::time::Duration::from_millis(250)).await;
    }
    Err(err(format!(
        "turn {turn_hash} accepted but not receipted within 30s"
    )))
}

#[tokio::main]
async fn main() {
    // Route this process's ML-DSA through the Lean-verified cores exported by
    // the linked archive (once-per-process, the same install the node and the
    // SDK agent-runtime perform). Without it dregg-pq's audit gate ABORTS the
    // first hybrid sign rather than silently running the unaudited `fips204`
    // crate — the gate is right, the host must install.
    let sign_core = dregg_sdk::install_verified_mldsa_sign_core_real();
    let verify_core = dregg_sdk::install_verified_mldsa_verify_core();
    eprintln!("[client-sign] verified ML-DSA cores: sign {sign_core:?}, verify {verify_core:?}");

    let mut argv: Vec<String> = std::env::args().skip(1).collect();
    if argv.is_empty() {
        eprintln!("{USAGE}");
        std::process::exit(2);
    }
    let cmd = argv.remove(0);
    let run = async {
        let flags = parse_flags(argv)?;
        match cmd.as_str() {
            "join" => cmd_join(flags).await,
            "send" => cmd_send(flags).await,
            _ => Err(err(format!("unknown verb '{cmd}' (try --help)"))),
        }
    };
    if let Err(e) = run.await {
        eprintln!("[client-sign] error: {e}");
        std::process::exit(1);
    }
}
