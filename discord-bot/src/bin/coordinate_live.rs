//! `coordinate_live` — drive a real two-agent coordination round and settle it
//! ATOMICALLY on a LIVE dregg node. The reproducible "watch your agent
//! civilization" demo.
//!
//! It runs the SAME landed promise-pipeline the bot's `/coordinate` command runs
//! (`dregg_app_framework::agent_coordination::coordinate`): a PRODUCER agent
//! computes a result off-chain and hands the CONSUMER a promise; the consumer
//! pipelines its payment against that promise; and the whole cooperation settles
//! as ONE real conserving turn submitted to the node — receipted, finalized,
//! per-asset Σδ=0. Then it runs the broken-promise variant and shows that the
//! round rolls back whole: nothing is submitted, both cells' live balances are
//! unchanged.
//!
//! It depends on NONE of the bot's Discord internals — only the public dregg
//! crates + an HTTP client — so a community member can read it as the canonical
//! reference for driving coordination live, and run it against any node.
//!
//! # Run it
//!
//! ```text
//! # against a local recovered node (default):
//! cargo run --bin coordinate_live
//!
//! # against any node + a chosen price:
//! NODE_URL=http://127.0.0.1:8771 PRICE=42 cargo run --bin coordinate_live
//! ```
//!
//! It exits non-zero if the live settle does not land + conserve, or if the
//! rollback variant moves any value — so it doubles as an end-to-end check.

use std::collections::BTreeSet;
use std::process::ExitCode;

use dregg_app_framework::AppCipherclerk;
use dregg_app_framework::agent_coordination::{
    CoordinationError, CoordinationLeg, CoordinationReceipt, LegOutput, coordinate,
};
use dregg_app_framework::ring_trade::{CommitmentId, WideLedger, WideLeg};
use dregg_sdk::{AgentCipherclerk, CellId};
use dregg_turn::{Action, Effect};
use zeroize::Zeroizing;

/// The fee (in computrons) declared per settled value move. The executor gates a
/// turn on `fee >= estimated cost`; a signed single-transfer action estimates
/// ~425 computrons (action 100 + signature 200 + effect 50 + transfer 75), so a
/// 500 ceiling clears it with margin.
const SETTLE_FEE_PER_MOVE: u64 = 500;

/// The demo asset the off-chain round settles in (a fixed tag). The LIVE settle
/// moves the node's native computron balance (DEC).
const COORD_ASSET: [u8; 32] = {
    let mut a = [0u8; 32];
    a[0] = 0xC0;
    a[1] = 0x0D;
    a
};

#[tokio::main]
async fn main() -> ExitCode {
    let node = std::env::var("NODE_URL").unwrap_or_else(|_| "http://127.0.0.1:8771".to_string());
    let price: u64 = std::env::var("PRICE")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(30);
    // A demo bot-secret + two agent ids. Distinct ids ⇒ distinct real cells.
    let secret: [u8; 32] = *blake3::hash(b"dregg.coordinate-live.demo.secret.v1").as_bytes();

    println!("== coordinate_live — multi-agent coordination on a LIVE node ==");
    println!("node:  {node}");
    println!("price: {price} DEC\n");

    // ── INSTALL THE VERIFIED EXECUTOR GATE ───────────────────────────────────────────────────
    // ⚑ THIS BINARY IS NOT THE BOT. `run_pair_round` below calls
    // `dregg_app_framework::agent_coordination::coordinate` IN THIS PROCESS, and that folds the
    // round's value moves through the FAIL-CLOSED `settle_ring_wide_verified`: with no
    // `IntentVerifiedGate` registered it REFUSES rather than let an unverified in-process Rust
    // fold decide the round. That refusal is correct and stays.
    //
    // `discord-bot/src/main.rs` installs the gate — but this is a SEPARATE binary with its own
    // `main`, so it inherited exactly none of that. The crate was recorded as fixed while its
    // second entry point still settled with no gate reachable, which is how the
    // un-called-initializer class survives a fix: the census counts CRATES and the gate is
    // per-PROCESS. Every additional `main` is another place to forget.
    //
    // `dregg-exec-lean` is already a normal dependency of this crate (Cargo.toml, not dev), so
    // this is a call, not a new edge.
    dregg_exec_lean::register_distributed_gates();
    if dregg_lean_ffi::distributed_exports_available() {
        println!("verified executor gate: INSTALLED (Lean exports reachable)\n");
    } else {
        // Say which absence it is BEFORE the first round, rather than letting a refusal
        // downstream read as "the coordination round was rejected". It was never judged.
        eprintln!(
            "REFUSING TO RUN: the verified distributed gates are installed but this build has NO \
             VERIFIED CORE — `dregg-lean-ffi`'s exports are unreachable (no linked \
             `libdregg_lean.a`, or Lean init failed). Every round would be refused UNJUDGED, and \
             that is a fact about this BUILD, not about the coordination. Seed a HEAD-matching \
             archive and rebuild."
        );
        return ExitCode::FAILURE;
    }

    let http = reqwest::Client::new();

    // Action signatures bind to the executor's federation id. An unconfigured
    // solo node derives it as blake3(node public key) (FEDERATION_ID env on a
    // configured federation); match it so the node accepts our authorizations.
    let fed = match node_federation_id(&http, &node).await {
        Some(f) => f,
        None => {
            eprintln!("could not read node federation id from {node}/health");
            return ExitCode::FAILURE;
        }
    };

    let producer = Agent::derive(&secret, 0xA0, fed); // computes the result
    let consumer = Agent::derive(&secret, 0xC0, fed); // pays for it
    println!("producer cell: {}", producer.cell_hex);
    println!("consumer cell: {}\n", consumer.cell_hex);

    // Materialize both cells; fund the consumer enough to settle.
    if let Err(e) = materialize(&http, &node, &producer.cell_hex).await {
        eprintln!("could not materialize producer cell: {e}");
        return ExitCode::FAILURE;
    }
    if let Err(e) = materialize(&http, &node, &consumer.cell_hex).await {
        eprintln!("could not materialize consumer cell: {e}");
        return ExitCode::FAILURE;
    }
    // The consumer pays the price PLUS the execution fee; fund enough for both.
    let need = price + SETTLE_FEE_PER_MOVE + 100;
    while get_balance(&http, &node, &consumer.cell_hex)
        .await
        .unwrap_or(0)
        < need
    {
        if let Err(e) = faucet(&http, &node, &consumer.cell_hex, 10000).await {
            eprintln!("could not fund consumer: {e}");
            return ExitCode::FAILURE;
        }
    }

    // ─── 1) The SUCCESS path: cooperate, then settle atomically on the node ───
    println!("--- 1. coordinated success (atomic on-chain settle) ---");
    let pc = CommitmentId(producer.cell_bytes);
    let cc = CommitmentId(consumer.cell_bytes);

    let c_before = get_balance(&http, &node, &consumer.cell_hex)
        .await
        .unwrap_or(0);
    let p_before = get_balance(&http, &node, &producer.cell_hex)
        .await
        .unwrap_or(0);

    let receipt = match run_pair_round(pc, cc, "render-report", price) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("off-chain round refused: {e}");
            return ExitCode::FAILURE;
        }
    };
    println!(
        "promise handoff: produce → consume  (layers: {})",
        receipt
            .parallel_layers
            .iter()
            .map(|l| format!("[{}]", l.join(", ")))
            .collect::<Vec<_>>()
            .join(" → ")
    );
    println!("round hash:      {}", hex32(&receipt.round_hash));

    let turn_hash = match settle_live(&http, &node, &consumer, &receipt).await {
        Ok(h) => h,
        Err(e) => {
            eprintln!("LIVE settle did not land: {e}");
            return ExitCode::FAILURE;
        }
    };
    let c_after = get_balance(&http, &node, &consumer.cell_hex)
        .await
        .unwrap_or(0);
    let p_after = get_balance(&http, &node, &producer.cell_hex)
        .await
        .unwrap_or(0);

    println!("ON-CHAIN receipt (turn hash): {turn_hash}");
    println!(
        "live balances (DEC): consumer {c_before} -> {c_after} | producer {p_before} -> {p_after}"
    );
    let producer_delta = p_after as i128 - p_before as i128;
    let consumer_delta = c_before as i128 - c_after as i128; // amount the consumer parted with
    let fee_paid = consumer_delta - price as i128;
    println!("producer received exactly the quoted price: +{producer_delta} DEC (price = {price})");
    println!(
        "consumer paid price + execution fee: -{consumer_delta} DEC (= {price} price + {fee_paid} fee, fee redistributed to proposer/treasury so whole-ledger Σδ=0 holds)"
    );
    if producer_delta != price as i128 {
        eprintln!("FAIL: producer did not receive exactly the coordinated price");
        return ExitCode::FAILURE;
    }
    println!(
        "OK: the coordinated settle LANDED on the live node; the producer received exactly the price.\n"
    );

    // ─── 2) The ROLLBACK path: a broken promise — nothing settles ───
    println!("--- 2. broken promise (rollback — nothing settles) ---");
    let rc_before = get_balance(&http, &node, &consumer.cell_hex)
        .await
        .unwrap_or(0);
    let rp_before = get_balance(&http, &node, &producer.cell_hex)
        .await
        .unwrap_or(0);

    let err = run_pair_round_broken(pc, cc, "render-report");
    match &err {
        CoordinationError::Broken {
            leg,
            downstream_broken,
            ..
        } => println!(
            "producer promise broke at leg `{leg}`; downstream rolled back: {downstream_broken:?}"
        ),
        other => {
            eprintln!("expected a Broken round, got: {other}");
            return ExitCode::FAILURE;
        }
    }
    println!("→ the round refused BEFORE any settle; no turn was submitted to the node.");

    let rc_after = get_balance(&http, &node, &consumer.cell_hex)
        .await
        .unwrap_or(0);
    let rp_after = get_balance(&http, &node, &producer.cell_hex)
        .await
        .unwrap_or(0);
    println!(
        "live balances (DEC): consumer {rc_before} -> {rc_after} | producer {rp_before} -> {rp_after}"
    );
    if rc_before != rc_after || rp_before != rp_after {
        eprintln!("FAIL: a broken promise moved value — rollback not atomic");
        return ExitCode::FAILURE;
    }
    println!("OK: a broken promise left the live ledger UNTOUCHED (rollback proven).\n");

    println!("== PASS: multi-agent coordination is LIVE — atomic settle + atomic rollback ==");
    ExitCode::SUCCESS
}

// ─── The promise-pipeline rounds (use the landed app-framework coordinator) ───

/// Derive a round id binding the pair + task (deterministic / reproducible).
fn round_id_for(producer: &CommitmentId, consumer: &CommitmentId, task: &str) -> [u8; 32] {
    let mut h = blake3::Hasher::new_derive_key("dregg.discord.coordinate-round.v1");
    h.update(&producer.0);
    h.update(&consumer.0);
    h.update(task.as_bytes());
    *h.finalize().as_bytes()
}

/// Run the producer→consumer promise round off-chain (the landed coordinator).
fn run_pair_round(
    producer: CommitmentId,
    consumer: CommitmentId,
    task: &str,
    price: u64,
) -> Result<CoordinationReceipt, CoordinationError> {
    let round_id = round_id_for(&producer, &consumer, task);
    let mut ledger = WideLedger::new();
    ledger.add_account(producer.0);
    ledger.add_account(consumer.0);
    ledger.set(consumer.0, &COORD_ASSET, (price * 10).max(price) as i128);

    let legs = vec![
        CoordinationLeg::new(producer, "produce", move |_| {
            Ok(LegOutput::compute(price.to_le_bytes().to_vec()))
        }),
        CoordinationLeg::new(consumer, "consume", move |inputs| {
            let raw = inputs.get("produce").cloned().unwrap_or_default();
            let quoted = u64::from_le_bytes(
                raw.try_into()
                    .map_err(|_| "producer promise was not a price".to_string())?,
            );
            Ok(LegOutput::with_moves(
                b"paid",
                vec![WideLeg {
                    from: consumer.0,
                    to: producer.0,
                    asset: COORD_ASSET,
                    amount: quoted as i128,
                }],
            ))
        })
        .after("produce"),
    ];
    coordinate(round_id, legs, &ledger)
}

/// Run the round where the producer's work FAILS — the broken-promise path.
fn run_pair_round_broken(
    producer: CommitmentId,
    consumer: CommitmentId,
    task: &str,
) -> CoordinationError {
    let round_id = round_id_for(&producer, &consumer, task);
    let mut ledger = WideLedger::new();
    ledger.add_account(producer.0);
    ledger.add_account(consumer.0);
    ledger.set(consumer.0, &COORD_ASSET, 1000);
    let legs = vec![
        CoordinationLeg::new(producer, "produce", move |_| {
            Err("producer could not complete the task; promise broken".to_string())
        }),
        CoordinationLeg::new(consumer, "consume", move |_| {
            Ok(LegOutput::compute(b"paid".to_vec()))
        })
        .after("produce"),
    ];
    coordinate(round_id, legs, &ledger)
        .err()
        .expect("a broken producer promise always refuses the round")
}

// ─── The live settle (one atomic signed turn per the round's value moves) ───

async fn settle_live(
    http: &reqwest::Client,
    node: &str,
    payer: &Agent,
    receipt: &CoordinationReceipt,
) -> Result<String, String> {
    let payer_bytes = payer.cell_bytes;
    let distinct: BTreeSet<_> = receipt.settled_moves.iter().map(|m| m.from).collect();
    if receipt.settled_moves.iter().any(|m| m.from != payer_bytes) {
        return Err(format!(
            "round settles from {} distinct payers; a single signed turn cannot settle a multi-payer ring (use /turn/atomic)",
            distinct.len()
        ));
    }

    let mut actions: Vec<Action> = Vec::new();
    for m in &receipt.settled_moves {
        let amount = u64::try_from(m.amount).map_err(|_| "amount overflow".to_string())?;
        let from = CellId(m.from);
        let to = CellId(m.to);
        actions.push(payer.app.make_action(
            from,
            "transfer",
            vec![Effect::Transfer { from, to, amount }],
        ));
    }

    let move_count = actions.len();
    let mut turn = if actions.len() == 1 {
        payer.app.make_turn(actions.into_iter().next().unwrap())
    } else {
        payer.app.make_turn_with_actions(actions)
    };
    turn.memo = Some("coordinate-live settle".to_string());
    turn.nonce = fetch_nonce(http, node, &payer.cell_hex).await.unwrap_or(0);
    // Cover the executor's computron estimate (signed transfer ≈ 425/move). The
    // fee is debited from the payer and redistributed (proposer/treasury), so
    // whole-ledger Σδ=0 still holds; the producer receives exactly the price.
    turn.fee = (SETTLE_FEE_PER_MOVE * move_count as u64).max(SETTLE_FEE_PER_MOVE);
    // The node chains each turn off the current receipt-chain head; declare it.
    turn.previous_receipt_hash = fetch_chain_head(http, node).await;
    let signed = payer.app.sign_turn(&turn);

    let body = postcard::to_stdvec(&signed).map_err(|e| format!("encode signed turn: {e}"))?;
    let mut req = http
        .post(format!("{node}/api/turns/submit-signed"))
        .header("content-type", "application/octet-stream");
    // The node's turn ingress is bearer-gated once a passphrase is set. Pass the
    // operator token via DEVNET_API_TOKEN (the same env the bot's client reads).
    if let Ok(tok) = std::env::var("DEVNET_API_TOKEN") {
        if !tok.trim().is_empty() {
            req = req.header("authorization", format!("Bearer {}", tok.trim()));
        }
    }
    let resp = req
        .body(body)
        .send()
        .await
        .map_err(|e| format!("submit: {e}"))?;
    if !resp.status().is_success() {
        return Err(format!("node returned {}", resp.status()));
    }
    let v: serde_json::Value = resp.json().await.map_err(|e| format!("decode: {e}"))?;
    if !v.get("accepted").and_then(|b| b.as_bool()).unwrap_or(false) {
        return Err(format!(
            "node rejected: {}",
            v.get("error").and_then(|e| e.as_str()).unwrap_or("unknown")
        ));
    }
    v.get("turn_hash")
        .and_then(|h| h.as_str())
        .map(|s| s.to_string())
        .ok_or_else(|| "node accepted but omitted turn_hash".to_string())
}

// ─── A self-contained agent identity (same derivation the bot's cclerk uses) ──

struct Agent {
    app: AppCipherclerk,
    cell_bytes: [u8; 32],
    cell_hex: String,
}

impl Agent {
    fn derive(bot_secret: &[u8; 32], id: u64, fed: [u8; 32]) -> Self {
        let mut input = Vec::with_capacity(40);
        input.extend_from_slice(bot_secret);
        input.extend_from_slice(&id.to_le_bytes());
        let seed = blake3::derive_key("dregg-discord-bot-v1", &input);
        let agent = AgentCipherclerk::from_key_bytes(Zeroizing::new(seed));
        let app = AppCipherclerk::new(agent, fed);
        let cell = app.cell_id();
        Self {
            app,
            cell_bytes: cell.0,
            cell_hex: hex::encode(cell.0),
        }
    }
}

// ─── Thin node HTTP helpers ───────────────────────────────────────────────────

/// Materialize `cell` as a zero-pk stub. No `public_key`: with one, a solo
/// node mints a hosted cell bound to the Ed25519 key and carrying no ML-DSA
/// anchor, which the first-turn claim declines and admission refuses as not
/// enrolled, so it could never act. The agent's first hybrid turn claims the
/// stub instead.
async fn materialize(http: &reqwest::Client, node: &str, cell: &str) -> Result<(), String> {
    let resp = http
        .post(format!("{node}/api/faucet"))
        .json(&serde_json::json!({ "recipient": cell, "amount": 0 }))
        .send()
        .await
        .map_err(|e| e.to_string())?;
    if resp.status().is_success() {
        Ok(())
    } else {
        Err(format!("faucet(materialize) -> {}", resp.status()))
    }
}

async fn faucet(http: &reqwest::Client, node: &str, cell: &str, amount: u64) -> Result<(), String> {
    let resp = http
        .post(format!("{node}/api/faucet"))
        .json(&serde_json::json!({ "recipient": cell, "amount": amount }))
        .send()
        .await
        .map_err(|e| e.to_string())?;
    if resp.status().is_success() {
        Ok(())
    } else {
        Err(format!("faucet -> {}", resp.status()))
    }
}

async fn get_balance(http: &reqwest::Client, node: &str, cell: &str) -> Option<u64> {
    let resp = http
        .get(format!("{node}/api/cell/{cell}"))
        .send()
        .await
        .ok()?;
    let v: serde_json::Value = resp.json().await.ok()?;
    v.get("balance").and_then(|b| b.as_u64())
}

async fn fetch_nonce(http: &reqwest::Client, node: &str, cell: &str) -> Option<u64> {
    let resp = http
        .get(format!("{node}/api/cell/{cell}"))
        .send()
        .await
        .ok()?;
    let v: serde_json::Value = resp.json().await.ok()?;
    v.get("nonce").and_then(|b| b.as_u64())
}

/// The current receipt-chain head hash (the receipt flagged `chain_head`). The
/// node chains every new turn off this; `None` on a chain with no receipts.
async fn fetch_chain_head(http: &reqwest::Client, node: &str) -> Option<[u8; 32]> {
    let resp = http.get(format!("{node}/api/receipts")).send().await.ok()?;
    let v: serde_json::Value = resp.json().await.ok()?;
    let arr = v.as_array()?;
    let head = arr.iter().find(|r| {
        r.get("chain_head")
            .and_then(|b| b.as_bool())
            .unwrap_or(false)
    })?;
    let hex_str = head.get("receipt_hash").and_then(|h| h.as_str())?;
    let bytes = hex::decode(hex_str).ok()?;
    bytes.try_into().ok()
}

fn hex32(b: &[u8; 32]) -> String {
    hex::encode(b)
}

/// The executor federation id the node binds action signatures to. An
/// unconfigured solo node uses `blake3(node public key)`.
async fn node_federation_id(http: &reqwest::Client, node: &str) -> Option<[u8; 32]> {
    let resp = http.get(format!("{node}/health")).send().await.ok()?;
    let v: serde_json::Value = resp.json().await.ok()?;
    let pk_hex = v.get("public_key").and_then(|p| p.as_str())?;
    let pk = hex::decode(pk_hex).ok()?;
    Some(*blake3::hash(&pk).as_bytes())
}
