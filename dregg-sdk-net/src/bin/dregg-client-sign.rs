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
//!          agent cell is faucet-materialized and funded to the requested floor.
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
/// The node accepts at most 10,000 computrons in one funded faucet request.
const FAUCET_MAX_GRANT: u64 = 10_000;
/// One refill must cover a bounded burst inside the faucet's 60-second per-cell window.
const SEND_FUNDING_HORIZON: u64 = 6;

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

fn build_chat_turn(
    clerk: &AgentCipherclerk,
    cell: dregg_sdk::CellId,
    topic: &str,
    payload: &str,
    federation_id: &[u8; 32],
    nonce: u64,
) -> Turn {
    let effect = Effect::EmitEvent {
        cell,
        event: Event {
            topic: symbol(topic),
            data: pack_payload(payload.as_bytes()),
        },
    };
    let action = clerk.sign_action_hybrid(
        dregg_sdk::raw::unsigned_action_named(cell, topic, vec![effect]),
        federation_id,
        nonce,
    );
    let mut turn = clerk.make_turn_with_actions(vec![action]);
    turn.agent = cell;
    turn.nonce = nonce;
    turn.memo = Some(payload.to_string());
    turn.valid_until = Some(i64::MAX / 2);
    turn
}

/// The cost model the CLIENT estimates its declared `turn.fee` against.
///
/// This bin only ever builds a single-action `EmitEvent` turn
/// ([`build_chat_turn`]), which is exactly dregg's COORDINATION class
/// ([`Turn::is_coordination`]: EmitEvent-only, no `balance_change`). When the
/// deployment opts in via `DREGG_COORDINATION_EXEMPT` (truthy — helm forwards it
/// on the chat send path), the estimate carries `coordination_exempt = true`, so
/// [`TurnExecutor::estimate_cost`] returns 0 for the class and the client
/// declares `fee = 0`: the turn rides the node's coordination-exempt admission
/// free — no cell drain, no faucet grant, no `[unsigned]` throttle. Default OFF =
/// exact legacy behavior (estimate the full computron cost), so a non-exempt node
/// still gets a fully-funded fee.
fn fee_cost_model() -> ComputronCosts {
    let mut costs = ComputronCosts::default();
    if env("DREGG_COORDINATION_EXEMPT")
        .map(|v| matches!(v.trim().to_ascii_lowercase().as_str(), "1" | "true" | "yes" | "on"))
        .unwrap_or(false)
    {
        costs.coordination_exempt = true;
    }
    costs
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
        err(
            "the node's /turns/submit is bearer-protected: set DREGG_API_TOKEN \
             (or --token), or DREGG_NODE_PASSPHRASE to unlock"
                .to_string(),
        )
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

#[derive(Debug)]
struct FundingOutcome {
    materialized: bool,
    topped_up: bool,
    joined_in_flight: bool,
    balance: u64,
}

fn observed_balance(cell: &serde_json::Value) -> Result<Option<u64>> {
    if cell.get("found").and_then(|f| f.as_bool()) != Some(true) {
        return Ok(None);
    }
    let balance = cell
        .get("balance")
        .and_then(|b| b.as_i64())
        .ok_or_else(|| err(format!("cell response has no signed balance: {cell}")))?;
    if balance < 0 {
        return Err(err(format!(
            "agent cell has negative balance {balance}; refusing to hide an issuer-well state"
        )));
    }
    Ok(Some(balance as u64))
}

/// Return whether the cell is absent and how many computrons are required to
/// make it spendable. `minimum_balance` is the next turn's actual fee; only a
/// balance below that threshold opens the faucet. When it does, replenish to
/// `target_balance` so rapid subsequent sends do not hit the 1/min faucet limit.
fn funding_shortfall(
    cell: &serde_json::Value,
    minimum_balance: u64,
    target_balance: u64,
) -> Result<(bool, u64)> {
    if target_balance < minimum_balance {
        return Err(err(format!(
            "funding target {target_balance} is below required minimum {minimum_balance}"
        )));
    }
    match observed_balance(cell)? {
        Some(balance) if balance >= minimum_balance => Ok((false, 0)),
        Some(balance) => Ok((false, target_balance.saturating_sub(balance))),
        None => Ok((true, target_balance)),
    }
}

async fn wait_for_balance(
    http: &reqwest::Client,
    cell_url: &str,
    target_balance: u64,
) -> Result<Option<u64>> {
    for _ in 0..40 {
        let current = get_json(http, cell_url).await?;
        if let Some(balance) = observed_balance(&current)?
            && balance >= target_balance
        {
            return Ok(Some(balance));
        }
        tokio::time::sleep(std::time::Duration::from_millis(250)).await;
    }
    Ok(None)
}

/// Ensure the profile's canonical cell exists and is spendable at
/// `minimum_balance`. An existing depleted cell is not "done": request enough
/// from the owner faucet to reach `target_balance`, require a committed faucet
/// turn for a positive top-up, then poll until the authoritative balance rises.
/// A rate-limit refusal can mean another owner already submitted the identical
/// full-mode grant; in that case join the in-flight authority by polling rather
/// than issuing a duplicate or failing before finalization lands.
async fn ensure_cell(
    http: &reqwest::Client,
    node_url: &str,
    cell_hex: &str,
    pk_hex: &str,
    minimum_balance: u64,
    target_balance: u64,
) -> Result<FundingOutcome> {
    let cell_url = format!("{node_url}/api/cell/{cell_hex}");
    let initial = get_json(http, &cell_url).await?;
    let (materialized, shortfall) = funding_shortfall(&initial, minimum_balance, target_balance)?;
    if !materialized && shortfall == 0 {
        return Ok(FundingOutcome {
            materialized: false,
            topped_up: false,
            joined_in_flight: false,
            balance: observed_balance(&initial)?.expect("existing cell has a balance"),
        });
    }

    let raw = http
        .post(format!("{node_url}/api/faucet"))
        .json(&serde_json::json!({
            "recipient": cell_hex,
            "amount": shortfall,
            "public_key": pk_hex,
        }))
        .send()
        .await
        .map_err(|e| err(format!("POST /api/faucet: {e}")))?;
    let status = raw.status();
    let body = raw
        .text()
        .await
        .map_err(|e| err(format!("read faucet response: {e}")))?;
    if !status.is_success() {
        return Err(err(format!("POST /api/faucet returned {status}: {body}")));
    }
    let resp: serde_json::Value = serde_json::from_str(&body)
        .map_err(|e| err(format!("parse faucet response (HTTP {status}): {e}")))?;
    if resp.get("success").and_then(|s| s.as_bool()) != Some(true) {
        let reason = resp
            .get("error")
            .and_then(|e| e.as_str())
            .unwrap_or_default();
        if shortfall > 0 && reason.starts_with("rate limited") {
            if let Some(balance) = wait_for_balance(http, &cell_url, target_balance).await? {
                eprintln!(
                    "[client-sign] joined an in-flight faucet grant; balance reached {balance}"
                );
                return Ok(FundingOutcome {
                    materialized: false,
                    topped_up: false,
                    joined_in_flight: true,
                    balance,
                });
            }
            return Err(err(format!(
                "faucet grant was already in flight but cell {cell_hex} did not reach {target_balance} computrons within 10s: {resp}"
            )));
        }
        return Err(err(format!("faucet refused funding: {resp}")));
    }
    if shortfall > 0 && resp.get("turn_hash").and_then(|h| h.as_str()).is_none() {
        return Err(err(format!(
            "faucet reported success for +{shortfall} computrons without a committed turn_hash: {resp}"
        )));
    }

    let action = if materialized {
        "materialized"
    } else {
        "topped up"
    };
    eprintln!("[client-sign] faucet {action} cell (+{shortfall} computrons)");
    if let Some(balance) = wait_for_balance(http, &cell_url, target_balance).await? {
        return Ok(FundingOutcome {
            materialized,
            topped_up: !materialized && shortfall > 0,
            joined_in_flight: false,
            balance,
        });
    }
    Err(err(format!(
        "cell {cell_hex} did not reach the {target_balance}-computron funding target within 10s after faucet accept"
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
        let info =
            profiles::create(&name).map_err(|e| err(format!("create profile '{name}': {e}")))?;
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
       ensure the profile identity + a cell funded to at least N computrons\n\
  send [--profile P] [--node-url U] [--token T] [--fund N] [--topic S] [--to CELL_HEX] PAYLOAD...\n\
       ensure at least N computrons, then commit ONE hybrid-signed EmitEvent; payload\n\
       rides in the signed turn (memo + event data words)\n\n\
env (flags win): DREGG_NODE_URL, DREGG_API_TOKEN (or DREGG_NODE_PASSPHRASE\n\
to unlock), DREGG_PROFILE (the SDK's active-profile convention)";

async fn cmd_join(f: Flags) -> Result<()> {
    let http = reqwest::Client::new();
    let (name, clerk) = resolve_clerk(f.profile.as_deref(), true)?;
    let cell_hex = hex::encode(clerk.cell_id("default").as_bytes());
    let pk_hex = hex::encode(clerk.public_key().0);
    let funding = ensure_cell(&http, &f.node_url, &cell_hex, &pk_hex, f.fund, f.fund).await?;
    println!(
        "{}",
        serde_json::json!({
            "joined": true,
            "node": f.node_url,
            "profile": name,
            "public_key": pk_hex,
            "cell": cell_hex,
            "materialized": funding.materialized,
            "topped_up": funding.topped_up,
            "joined_in_flight": funding.joined_in_flight,
            "balance": funding.balance,
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

    // Materialize first without consuming the funded faucet bucket. The zero-
    // amount path is explicitly outside the per-cell 1/min limit, so a brand-new
    // profile can immediately receive the fee-sized positive top-up below.
    let pk_hex = hex::encode(clerk.public_key().0);
    let presence = ensure_cell(&http, &f.node_url, &cell_hex, &pk_hex, 0, 0).await?;

    let federation_id = node
        .fetch_executor_federation_id()
        .await
        .map_err(|e| err(format!("fetch executor federation id: {e}")))?;
    let estimate_nonce = node
        .fetch_cell_nonce(&cell)
        .await
        .map_err(|e| err(format!("fetch own-cell nonce for fee estimate: {e}")))?;
    let mut turn = build_chat_turn(
        &clerk,
        cell,
        &f.topic,
        &payload,
        &federation_id,
        estimate_nonce,
    );
    // Coordination-aware estimate: `fee = 0` when opted in (this is always an
    // EmitEvent-only turn), so the send rides dregg's exempt admission free.
    turn.fee = TurnExecutor::new(fee_cost_model()).estimate_cost(&turn);

    // Funding is SEND correctness, not a one-time join convenience. One grant
    // reserves a bounded six-send burst inside the faucet's 60-second window;
    // cap the requested delta to the node's 10,000-computron per-request law.
    let desired = f.fund.max(turn.fee.saturating_mul(SEND_FUNDING_HORIZON));
    let target = desired.min(presence.balance.saturating_add(FAUCET_MAX_GRANT));
    if target < turn.fee {
        return Err(err(format!(
            "turn fee {} exceeds the current balance {} plus the faucet's {}-computron grant cap",
            turn.fee, presence.balance, FAUCET_MAX_GRANT
        )));
    }
    let funding = ensure_cell(&http, &f.node_url, &cell_hex, &pk_hex, turn.fee, target).await?;

    // Funding can wait up to 10s and another same-profile sender can commit in
    // that window. Refetch the nonce immediately before signing, then rebuild
    // the action because dregg-action-sig-v3 binds that nonce.
    let nonce = node
        .fetch_cell_nonce(&cell)
        .await
        .map_err(|e| err(format!("refetch own-cell nonce after funding: {e}")))?;
    turn = build_chat_turn(&clerk, cell, &f.topic, &payload, &federation_id, nonce);
    turn.fee = TurnExecutor::new(fee_cost_model()).estimate_cost(&turn);
    if turn.fee > funding.balance {
        return Err(err(format!(
            "final turn fee {} exceeds the observed funded balance {}",
            turn.fee, funding.balance
        )));
    }
    turn.previous_receipt_hash = node
        .fetch_chain_head()
        .await
        .map_err(|e| err(format!("fetch chain head after funding: {e}")))?;
    let bearer = ensure_token(&http, &f.node_url, f.token.clone()).await?;

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
                    "materialized": presence.materialized,
                    "topped_up": funding.topped_up,
                    "joined_in_flight": funding.joined_in_flight,
                    "balance_before_send": funding.balance,
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

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
    use dregg_turn::{Action, Authorization, CallForest, DelegationMode, TurnResult, turn::Turn};
    use tokio::io::{AsyncReadExt, AsyncWriteExt};
    use tokio::net::TcpListener;
    use tokio::sync::Mutex;

    use super::*;

    #[derive(Clone, Copy)]
    enum FaucetMode {
        Commit,
        RateLimitedThenCommit,
    }

    struct FaucetNode {
        ledger: Ledger,
        faucet: CellId,
        recipient: CellId,
        calls: u64,
        mode: FaucetMode,
    }

    fn open_permissions() -> Permissions {
        Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        }
    }

    fn test_node(balance: i64, mode: FaucetMode) -> FaucetNode {
        let mut faucet = Cell::with_balance([1; 32], [0; 32], 1_000_000);
        faucet.permissions = open_permissions();
        let faucet_id = faucet.id();
        let mut recipient = Cell::with_balance([2; 32], [0; 32], balance);
        recipient.permissions = open_permissions();
        let recipient_id = recipient.id();
        let mut ledger = Ledger::new();
        ledger.insert_cell(faucet).unwrap();
        ledger.insert_cell(recipient).unwrap();
        FaucetNode {
            ledger,
            faucet: faucet_id,
            recipient: recipient_id,
            calls: 0,
            mode,
        }
    }

    fn transfer_turn(node: &FaucetNode, amount: u64) -> Turn {
        let mut forest = CallForest::new();
        forest.add_root(Action {
            target: node.faucet,
            method: *blake3::hash(b"faucet_transfer").as_bytes(),
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Default::default(),
            effects: vec![Effect::Transfer {
                from: node.faucet,
                to: node.recipient,
                amount,
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        });
        Turn {
            agent: node.faucet,
            nonce: node
                .ledger
                .get(&node.faucet)
                .expect("faucet cell")
                .state
                .nonce(),
            fee: 0,
            memo: None,
            valid_until: Some(1_000_000),
            call_forest: forest,
            depends_on: vec![],
            previous_receipt_hash: None,
            conservation_proof: None,
            sovereign_witnesses: Default::default(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        }
    }

    fn commit_top_up(node: &mut FaucetNode, amount: u64) -> serde_json::Value {
        let turn = transfer_turn(node, amount);
        let hash = hex::encode(turn.hash());
        node.calls += 1;
        match TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut node.ledger) {
            TurnResult::Committed { .. } => {
                serde_json::json!({"success": true, "turn_hash": hash})
            }
            other => serde_json::json!({"success": false, "error": format!("{other:?}")}),
        }
    }

    async fn handle_connection(mut socket: tokio::net::TcpStream, state: Arc<Mutex<FaucetNode>>) {
        let mut request = Vec::new();
        let mut chunk = [0u8; 4096];
        let header_end = loop {
            let Ok(n) = socket.read(&mut chunk).await else {
                return;
            };
            if n == 0 {
                return;
            }
            request.extend_from_slice(&chunk[..n]);
            if let Some(i) = request.windows(4).position(|w| w == b"\r\n\r\n") {
                break i + 4;
            }
        };
        let headers = String::from_utf8_lossy(&request[..header_end]).to_string();
        let content_length = headers
            .lines()
            .find_map(|line| {
                line.to_ascii_lowercase()
                    .strip_prefix("content-length:")
                    .and_then(|n| n.trim().parse::<usize>().ok())
            })
            .unwrap_or(0);
        while request.len() < header_end + content_length {
            let Ok(n) = socket.read(&mut chunk).await else {
                return;
            };
            if n == 0 {
                return;
            }
            request.extend_from_slice(&chunk[..n]);
        }
        let request_line = headers.lines().next().unwrap_or_default();
        let body = &request[header_end..header_end + content_length];
        let response = if request_line.starts_with("GET /api/cell/") {
            let node = state.lock().await;
            let balance = node
                .ledger
                .get(&node.recipient)
                .expect("recipient cell")
                .state
                .balance();
            serde_json::json!({"found": true, "balance": balance})
        } else if request_line.starts_with("POST /api/faucet ") {
            let amount = serde_json::from_slice::<serde_json::Value>(body)
                .ok()
                .and_then(|v| v.get("amount").and_then(|n| n.as_u64()))
                .unwrap_or(0);
            let mode = state.lock().await.mode;
            match mode {
                FaucetMode::Commit => {
                    let mut node = state.lock().await;
                    commit_top_up(&mut node, amount)
                }
                FaucetMode::RateLimitedThenCommit => {
                    state.lock().await.calls += 1;
                    let shared = state.clone();
                    tokio::spawn(async move {
                        tokio::time::sleep(std::time::Duration::from_millis(50)).await;
                        let mut node = shared.lock().await;
                        node.calls -= 1;
                        let _ = commit_top_up(&mut node, amount);
                    });
                    serde_json::json!({
                        "success": false,
                        "error": "rate limited: 1 request per cell per minute"
                    })
                }
            }
        } else {
            serde_json::json!({"error": "not found"})
        };
        let bytes = serde_json::to_vec(&response).unwrap();
        let head = format!(
            "HTTP/1.1 200 OK\r\ncontent-type: application/json\r\ncontent-length: {}\r\nconnection: close\r\n\r\n",
            bytes.len()
        );
        let _ = socket.write_all(head.as_bytes()).await;
        let _ = socket.write_all(&bytes).await;
    }

    async fn spawn_faucet_node(
        balance: i64,
        mode: FaucetMode,
    ) -> (String, Arc<Mutex<FaucetNode>>, tokio::task::JoinHandle<()>) {
        let state = Arc::new(Mutex::new(test_node(balance, mode)));
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let url = format!("http://{}", listener.local_addr().unwrap());
        let shared = state.clone();
        let handle = tokio::spawn(async move {
            while let Ok((socket, _)) = listener.accept().await {
                tokio::spawn(handle_connection(socket, shared.clone()));
            }
        });
        (url, state, handle)
    }

    fn real_chat_turn(agent: CellId, payload: &[u8]) -> Turn {
        let mut forest = CallForest::new();
        forest.add_root(Action {
            target: agent,
            method: *blake3::hash(b"helm.chat").as_bytes(),
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Default::default(),
            effects: vec![Effect::EmitEvent {
                cell: agent,
                event: Event {
                    topic: symbol("helm.chat"),
                    data: pack_payload(payload),
                },
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        });
        let mut turn = Turn {
            agent,
            nonce: 0,
            fee: 0,
            memo: Some(String::from_utf8(payload.to_vec()).unwrap()),
            valid_until: Some(1_000_000),
            call_forest: forest,
            depends_on: vec![],
            previous_receipt_hash: None,
            conservation_proof: None,
            sovereign_witnesses: Default::default(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        };
        turn.fee = TurnExecutor::new(ComputronCosts::default()).estimate_cost(&turn);
        turn
    }

    #[test]
    fn existing_low_balance_cell_requests_six_send_horizon() {
        let cell = serde_json::json!({"found": true, "balance": 90});
        assert_eq!(
            funding_shortfall(&cell, 1_510, 9_060).unwrap(),
            (false, 8_970)
        );
    }

    #[test]
    fn affordable_burst_send_does_not_reopen_rate_limited_faucet() {
        let cell = serde_json::json!({"found": true, "balance": 3_490});
        assert_eq!(funding_shortfall(&cell, 1_510, 9_060).unwrap(), (false, 0));
    }

    #[test]
    fn absent_cell_receives_the_full_funding_target() {
        let cell = serde_json::json!({"found": false, "balance": 0});
        assert_eq!(
            funding_shortfall(&cell, 1_510, 9_060).unwrap(),
            (true, 9_060)
        );
    }

    #[test]
    fn negative_agent_balance_refuses_instead_of_masking_an_issuer_well() {
        let cell = serde_json::json!({"found": true, "balance": -1});
        let error = funding_shortfall(&cell, 1_510, 9_060)
            .unwrap_err()
            .to_string();
        assert!(
            error.contains("negative balance -1"),
            "unexpected error: {error}"
        );
    }

    #[tokio::test]
    async fn low_balance_http_top_up_commits_and_enables_real_chat_turn() {
        let (url, state, handle) = spawn_faucet_node(90, FaucetMode::Commit).await;
        let (cell_hex, pk_hex, recipient) = {
            let node = state.lock().await;
            (
                hex::encode(node.recipient.0),
                hex::encode(node.ledger.get(&node.recipient).unwrap().public_key()),
                node.recipient,
            )
        };
        let payload = b"This chat-sized send must fail before funding and commit after the HTTP faucet top-up.";
        let turn = real_chat_turn(recipient, payload);
        assert!(turn.fee > 90 && turn.fee < 9_060);
        let mut depleted = state.lock().await.ledger.clone();
        let pre = TurnExecutor::new(ComputronCosts::default()).execute(&turn, &mut depleted);
        assert!(
            !pre.is_committed(),
            "must-fail-pre: the depleted real ledger must reject this exact chat turn: {pre:?}"
        );

        let http = reqwest::Client::new();
        let outcome = ensure_cell(&http, &url, &cell_hex, &pk_hex, 1_510, 9_060)
            .await
            .expect("existing low-balance cell must top up");
        assert!(outcome.topped_up);
        assert_eq!(outcome.balance, 9_060);
        let mut node = state.lock().await;
        assert_eq!(node.calls, 1, "the product path must call the faucet once");
        assert_eq!(
            node.ledger.get(&recipient).unwrap().state.balance(),
            9_060,
            "the committed HTTP top-up must raise the real ledger balance"
        );
        let result = TurnExecutor::new(ComputronCosts::default()).execute(&turn, &mut node.ledger);
        assert!(
            result.is_committed(),
            "the exact next metered chat turn must commit: {result:?}"
        );
        handle.abort();
    }

    #[tokio::test]
    async fn rate_limited_duplicate_joins_in_flight_grant() {
        let (url, state, handle) = spawn_faucet_node(90, FaucetMode::RateLimitedThenCommit).await;
        let (cell_hex, pk_hex) = {
            let node = state.lock().await;
            (
                hex::encode(node.recipient.0),
                hex::encode(node.ledger.get(&node.recipient).unwrap().public_key()),
            )
        };
        let outcome = ensure_cell(
            &reqwest::Client::new(),
            &url,
            &cell_hex,
            &pk_hex,
            1_510,
            9_060,
        )
        .await
        .expect("duplicate owner must join the in-flight grant");
        assert!(outcome.joined_in_flight);
        assert_eq!(outcome.balance, 9_060);
        assert_eq!(state.lock().await.calls, 1);
        handle.abort();
    }
}
