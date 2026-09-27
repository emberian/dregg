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
//!   transfer  move `--amount` computrons from the profile's own cell to
//!          `--to`. The signer is the SOURCE: `Effect::Transfer { from: own
//!          cell, to, amount }` on an action whose target is that same cell,
//!          so the executor gates the withdrawal on `Send` over the signed
//!          action. Exit 0 only when a receipt for EXACTLY this turn hash is
//!          on the node's chain at an accepted finality.
//!
//! Env (flags win): DREGG_NODE_URL (default http://127.0.0.1:8899),
//! DREGG_API_TOKEN (bearer for the protected ingress) or DREGG_NODE_PASSPHRASE
//! (unlock fallback), DREGG_PROFILE / the profiles `ACTIVE` file (the SDK's
//! own active-profile convention) when `--profile` is not given.

use dregg_sdk::AgentCipherclerk;
use dregg_sdk::profiles;
use dregg_sdk_net::NodeHttpClient;
use dregg_turn::action::{Action, Authorization, Effect, Event, symbol};
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

/// Parse a 32-byte cell id in the 64-character lowercase hex every dregg
/// surface spells cells with. A short, long, odd-length or non-hex value is a
/// hard error: a signer never guesses at the destination of value.
fn parse_cell_hex(what: &str, value: &str) -> Result<dregg_sdk::CellId> {
    let trimmed = value.trim();
    let bytes = hex::decode(trimmed)
        .map_err(|e| err(format!("{what} must be 64 hex characters (a 32-byte cell id): {e}")))?;
    let id: [u8; 32] = bytes.as_slice().try_into().map_err(|_| {
        err(format!(
            "{what} must be 64 hex characters (a 32-byte cell id); got {} bytes",
            bytes.len()
        ))
    })?;
    Ok(dregg_sdk::CellId(id))
}

/// Resolve a transfer's destination against the signer's own cell, returning
/// the canonical lowercase hex.
///
/// BOTH REFUSALS HERE ARE USABILITY REFUSALS, NOT THE AUTHORIZATION STORY, and
/// reading them as authorization would be a mistake. The authority to move
/// value OUT of the source is decided at its owning layer: the executor
/// requires `Send` on the action target for an `Effect::Transfer` whose `from`
/// is that target, and it requires the destination's `Receive` not to be
/// `AuthRequired::Impossible`. The client presents a signature and the executor
/// decides. What this function refuses is a caller mistake the executor would
/// happily commit: a transfer to the signer's OWN cell moves nothing and still
/// burns the fee.
///
/// Note that `send`'s guard is the OPPOSITE shape — it requires `--to` to BE
/// the signer's own cell, because a client-signed `EmitEvent` can only act as
/// the signer. Inverting that guard is NOT what makes a transfer authorized;
/// the two verbs simply refuse different caller mistakes.
fn resolve_destination(to: &str, own_cell_hex: &str, profile: &str) -> Result<String> {
    let dest = hex::encode(parse_cell_hex("--to", to)?.as_bytes());
    if dest.eq_ignore_ascii_case(own_cell_hex) {
        return Err(err(format!(
            "--to {dest} is profile '{profile}'s own cell: a self-transfer moves \
             nothing and still burns the turn fee"
        )));
    }
    Ok(dest)
}

/// Build the single-action TRANSFER turn: `Effect::Transfer { from, to, amount }`
/// on an action whose target IS `from`, hybrid-signed by the source's own key.
///
/// `Turn::hash` binds this effect: the effect's `from`, `to` and `amount` are
/// absorbed by `Effect::hash`, which the action hash absorbs, which the call
/// forest hash absorbs, which `dregg-turn-v3` absorbs alongside the agent, the
/// nonce and the fee. That chain is why a receipt matching this exact turn hash
/// is a statement about THIS transfer's recipient and amount, and not merely
/// about some turn of ours that committed.
fn build_transfer_turn(
    clerk: &AgentCipherclerk,
    from: dregg_sdk::CellId,
    to: dregg_sdk::CellId,
    amount: u64,
    federation_id: &[u8; 32],
    nonce: u64,
) -> Turn {
    let effect = Effect::Transfer { from, to, amount };
    let action = clerk.sign_action_hybrid(
        dregg_sdk::raw::unsigned_action_named(from, "transfer", vec![effect]),
        federation_id,
        nonce,
    );
    let mut turn = clerk.make_turn_with_actions(vec![action]);
    turn.agent = from;
    turn.nonce = nonce;
    turn.memo = None;
    turn.valid_until = Some(i64::MAX / 2);
    turn
}

/// The chat send's single action, UNSIGNED: one `EmitEvent` on `cell`.
fn chat_action(cell: dregg_sdk::CellId, topic: &str, payload: &str) -> Action {
    let effect = Effect::EmitEvent {
        cell,
        event: Event {
            topic: symbol(topic),
            data: pack_payload(payload.as_bytes()),
        },
    };
    dregg_sdk::raw::unsigned_action_named(cell, topic, vec![effect])
}

/// Wrap an already-authorized chat action in the send's turn envelope.
/// No signing happens here.
fn chat_turn(
    clerk: &AgentCipherclerk,
    cell: dregg_sdk::CellId,
    action: Action,
    nonce: u64,
    payload: &str,
) -> Turn {
    let mut turn = clerk.make_turn_with_actions(vec![action]);
    turn.agent = cell;
    turn.nonce = nonce;
    turn.memo = Some(payload.to_string());
    turn.valid_until = Some(i64::MAX / 2);
    turn
}

fn build_chat_turn(
    clerk: &AgentCipherclerk,
    cell: dregg_sdk::CellId,
    topic: &str,
    payload: &str,
    federation_id: &[u8; 32],
    nonce: u64,
) -> Turn {
    let action = clerk.sign_action_hybrid(chat_action(cell, topic, payload), federation_id, nonce);
    chat_turn(clerk, cell, action, nonce, payload)
}

/// The fee `build_chat_turn` would declare, computed WITHOUT signing.
///
/// `TurnExecutor::estimate_cost` reads the coordination class (effects and
/// `balance_change`), then per action `action_base`, the authorization
/// VARIANT (`HybridSignature` costs `2 * signature_verify`) and each effect's
/// cost. It never reads the nonce, the federation id, the memo or any
/// signature byte. So a `HybridSignature` with empty placeholder halves
/// estimates exactly what the signed turn estimates, at any nonce. The test
/// `unsigned_fee_estimate_equals_the_signed_turns_fee` holds that equality
/// against a really signed turn, so a future fee rule that reads signature
/// bytes fails there, not in production.
fn chat_fee(
    clerk: &AgentCipherclerk,
    costs: ComputronCosts,
    cell: dregg_sdk::CellId,
    topic: &str,
    payload: &str,
) -> u64 {
    let placeholder = Action {
        authorization: Authorization::HybridSignature {
            ed25519: [0u8; 64],
            ml_dsa: Vec::new(),
            ml_dsa_pk: Vec::new(),
        },
        ..chat_action(cell, topic, payload)
    };
    TurnExecutor::new(costs).estimate_cost(&chat_turn(clerk, cell, placeholder, 0, payload))
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

/// The two finality words `ReceiptInfo` can carry, lowercased. `Final` is a
/// BFT quorum (or a fast-path certificate with quorum signatures); `Tentative`
/// is one node in solo mode, safe only under a no-Byzantine assumption and
/// awaiting quorum validation on rejoin. A genesis-less single-operator devnet
/// downgrades EVERY committed receipt to `Tentative`, which is why accepting it
/// has to be the caller's explicit decision rather than this tool's default.
const FINALITY_FINAL: &str = "final";
const FINALITY_TENTATIVE: &str = "tentative";

/// What the node's own receipt chain says about EXACTLY ONE turn hash.
///
/// The distinction this type exists to keep is the one a consumer cannot make
/// for itself: a hash is not a commitment. The client-signed ingress returns a
/// `turn_hash` on REFUSAL as well as on success, and `accepted` is the node
/// saying it took the turn, not that the turn moved anything. Only a receipt
/// on the chain is the node's statement that the transfer committed, because
/// only a commit appends one.
#[derive(Debug, PartialEq, Eq)]
enum Commitment {
    /// A receipt for exactly this turn hash, at a finality the caller accepts.
    Committed {
        receipt_hash: String,
        chain_index: u64,
        finality: String,
    },
    /// No receipt for this hash yet. NOT a refusal — the turn may still commit.
    Pending,
    /// A receipt exists but its finality is below what the caller accepts.
    /// Also not a refusal: finality can rise.
    BelowFinality { finality: String },
    /// The node answered in a shape this reader cannot read. Never a
    /// commitment, and never a refusal either — it is UNKNOWN, and the caller
    /// is owed the reason rather than a verdict built on a guess.
    Unreadable(String),
}

/// Is a verified ML-DSA core the PRODUCER for this process, for both the
/// operations a transfer performs?
///
/// INSTALL IS ONCE PER PROCESS, so the SECOND call and every one after it
/// answers `AlreadyInstalled` — which the outcome's own documentation calls
/// healthy: "a core was already installed this process, crate still out of
/// TCB". Treating only `Installed` as healthy therefore meant that on a good
/// archive the FIRST arm ran and every later one silently skipped, reporting a
/// missing export that was not missing. At most one composed control could
/// ever execute, and a probe running first could skip them all.
///
/// Only `ExportAbsent` is unhealthy, and it is the one state that makes
/// signing abort.
fn cores_are_healthy(
    sign: dregg_sdk::MlDsaSignCoreRealInstall,
    keygen: dregg_sdk::MlDsaKeygenCoreRealInstall,
) -> bool {
    use dregg_sdk::{MlDsaKeygenCoreRealInstall as K, MlDsaSignCoreRealInstall as S};
    matches!(sign, S::Installed | S::AlreadyInstalled)
        && matches!(keygen, K::Installed | K::AlreadyInstalled)
}

/// EVERY EXIT AFTER THE SUBMISSION MAY HAVE REACHED THE NODE, in one shape.
///
/// A nonzero exit is not proof of refusal. Once the POST has left this
/// process, an HTTP status, a body this reader cannot parse, a missing or
/// unbindable hash, a dropped connection and a failed receipt query all say
/// the same thing about the money: UNKNOWN. A caller that reads any of them as
/// a refusal resubmits, and a resubmission moves the amount a second time.
///
/// A refusal DECIDED BEFORE THE SUBMISSION — bad flags, a self-transfer, a
/// source that cannot fund the turn — stays an ordinary error, because nothing
/// was attempted and there is nothing to be uncertain about.
fn unknown_after_submit(
    what: String,
    amount: u64,
    confirm_url: &str,
) -> Box<dyn std::error::Error> {
    err(format!(
        "{what}. This is UNKNOWN, not a refusal: the transfer may have \
         committed. Do NOT resubmit — a second transfer moves {amount} again. \
         Re-read the node with `curl '{confirm_url}'` and decide from that."
    ))
}

/// What a submit response says about the turn THIS process signed.
#[derive(Debug, PartialEq, Eq)]
enum Admission {
    /// The node took this exact turn. Admission, never commitment.
    Took,
    /// The node executed it and rejected it. Nothing moved, nothing to re-read.
    Refused(String),
    /// Anything else. The bytes may have been applied and this process cannot
    /// say, so it is UNKNOWN and the caller must not resubmit on it.
    Unknown(String),
}

/// Bind a submit response to the LOCALLY COMPUTED hash of the turn this
/// process signed.
///
/// THE WANTED HASH IS AN INPUT, and that is the whole point of this function
/// existing. Taking the hash from the RESPONSE and then confirming a receipt
/// for it produces a WRONG-OPERATION SUCCESS: a faulty or hostile node names
/// some other turn, that turn has a perfectly valid receipt, and the client
/// prints it beside THIS transfer's recipient and amount. A value mover must
/// never do that, so identity comes from the bytes it signed and the response
/// is only ever checked AGAINST it.
///
/// `submitted` NAMES WHAT THIS CALLER SIGNED, because both verbs share this
/// function and a reason that calls a send a "transfer" tells the operator
/// about an operation that did not happen. The word is the caller's and never
/// this function's to assume.
fn bind_admission(
    submitted: &str, local_hash: &str, verdict: &serde_json::Value,
) -> Admission {
    // IDENTITY IS ESTABLISHED BEFORE THE ANSWER IS TRUSTED, AND THAT ORDER IS
    // THE WHOLE POINT — IN BOTH DIRECTIONS. Deciding the refusal first made a
    // reply carrying NO hash, or SOMEONE ELSE'S, an ordinary decided refusal:
    // the caller was told nothing moved, on the strength of an answer that
    // never named this turn. The node's own reject path fills `turn_hash`
    // before it decides, so a refusal that does name this turn is real
    // evidence about it and a hashless or foreign one is not that evidence.
    match verdict.get("turn_hash").and_then(|h| h.as_str()) {
        Some(reported) if reported.eq_ignore_ascii_case(local_hash) => {}
        Some(reported) => {
            return Admission::Unknown(format!(
                "the node answered about turn {reported}, which is not the \
                 {submitted} this process signed ({local_hash})"
            ));
        }
        None => {
            return Admission::Unknown(format!(
                "the submit response carries no turn_hash, so it cannot be \
                 bound to the {submitted} this process signed"
            ));
        }
    }
    match verdict.get("accepted").and_then(|a| a.as_bool()) {
        // The node took THIS turn. Admission, never commitment.
        Some(true) => Admission::Took,
        // The node executed THIS turn, rejected it, and appended no receipt,
        // so nothing moved and there is nothing for a caller to re-read.
        Some(false) => Admission::Refused(
            verdict
                .get("error")
                .and_then(|e| e.as_str())
                .unwrap_or("no reason given")
                .to_string(),
        ),
        _ => Admission::Unknown(
            "the submit response says neither accepted nor refused".to_string(),
        ),
    }
}

/// The refusal that earns the one retry in [`submit_turn`]. A node that keeps
/// a head per agent says exactly this; a solo node built on 737a69fa4 says
/// `receipt chain mismatch: <the cipherclerk's reason>`.
const CHAIN_MISMATCH: &str = "receipt chain mismatch";

/// POST one serialized `SignedTurn` to the client-signed ingress and read the
/// answer. `Err` is every failure after the bytes left this process — the
/// connection, an HTTP status, a body that is not JSON — so the bytes may have
/// arrived and the ANSWER been lost. Each verb says what that means for it.
async fn post_turn(
    http: &reqwest::Client,
    node_url: &str,
    bearer: &str,
    bytes: Vec<u8>,
) -> std::result::Result<serde_json::Value, String> {
    let resp = http
        .post(format!("{node_url}/turns/submit"))
        .header("Content-Type", "application/octet-stream")
        .header("Authorization", format!("Bearer {bearer}"))
        .body(bytes)
        .send()
        .await
        .map_err(|e| format!("POST /turns/submit: {e}"))?;
    let status = resp.status();
    if !status.is_success() {
        return Err(format!("/turns/submit returned {status}"));
    }
    resp.json()
        .await
        .map_err(|e| format!("cannot parse the submit response: {e}"))
}

/// What a verb's submission ended as: the hash of the turn this process
/// signed LAST, and the node's answer about exactly that turn. `Err` in
/// `answer` is a failure after the POST left this process, which is UNKNOWN.
struct Submitted {
    turn_hash: String,
    answer: std::result::Result<Admission, String>,
}

/// Sign `turn`, submit it, and bind the answer to the turn signed.
///
/// THE AGENT'S OWN HEAD FIRST, THE NODE-WIDE HEAD ONCE. `turn` arrives
/// threaded on the agent's own receipt head, which a node that keeps a head per
/// agent requires. A solo node built on 737a69fa4 keeps ONE chain for the whole
/// node and appends every client receipt to it, so it refuses the agent's own
/// head with "receipt chain mismatch" whenever another agent committed since
/// this agent's last receipt, and for this agent's first turn on a non-empty
/// chain. That node rolls its ledger back before it answers, so the refused
/// turn appended nothing and moved nothing. The same turn, re-threaded on the
/// node-wide head and signed again, can therefore be submitted once more. Only
/// the envelope is re-signed: the action signature binds the nonce and the
/// federation, not the head. The new head changes `Turn::hash`, so the retry
/// is a different turn and its answer is bound to its own hash.
///
/// EXACTLY ONCE, AND ONLY ON THAT REFUSAL. Every other refusal, every UNKNOWN,
/// and the retry's own answer, whatever it is, go back to the caller as they
/// came. A second retry would only chase a head that every seat moves.
async fn submit_turn(
    http: &reqwest::Client,
    node: &NodeHttpClient,
    node_url: &str,
    bearer: &str,
    clerk: &AgentCipherclerk,
    turn: &mut Turn,
    submitted: &str,
) -> Result<Submitted> {
    let mut retried = false;
    loop {
        let signed = clerk.sign_turn(turn);
        let bytes =
            postcard::to_stdvec(&signed).map_err(|e| err(format!("serialize SignedTurn: {e}")))?;
        let turn_hash = hex::encode(signed.turn.hash());
        let answer = post_turn(http, node_url, bearer, bytes)
            .await
            .map(|verdict| bind_admission(submitted, &turn_hash, &verdict));
        match answer {
            Ok(Admission::Refused(why)) if !retried && why.starts_with(CHAIN_MISMATCH) => {
                // A decided refusal: nothing moved, so failing to read the
                // head for the retry is an ordinary error, not UNKNOWN.
                turn.previous_receipt_hash = node.fetch_chain_head().await.map_err(|e| {
                    err(format!(
                        "node refused the {submitted}: {why}; reading the node-wide \
                         receipt head for the one retry failed: {e}"
                    ))
                })?;
                eprintln!(
                    "[client-sign] retry: the node refused {submitted} {turn_hash} on the \
                     agent's own receipt head ({why}); resubmitting once on the node-wide head"
                );
                retried = true;
            }
            answer => return Ok(Submitted { turn_hash, answer }),
        }
    }
}

fn json_kind(v: &serde_json::Value) -> &'static str {
    match v {
        serde_json::Value::Null => "null",
        serde_json::Value::Bool(_) => "a boolean",
        serde_json::Value::Number(_) => "a number",
        serde_json::Value::String(_) => "a string",
        serde_json::Value::Array(_) => "an array",
        serde_json::Value::Object(_) => "an object",
    }
}

fn is_hash_hex(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|b| b.is_ascii_hexdigit())
}

/// Read the node's EXACT-turn-hash receipt query into a [`Commitment`].
///
/// `body` is the answer to `GET /api/starbridge/receipts?turn_hash=<hex>`,
/// which filters the WHOLE receipt chain by exact turn hash. That is the
/// instrument this reader wants and `GET /api/receipts` is not: the latter
/// serves only the newest 50 receipts, so on a busy node a committed turn falls
/// out of the window and a reader scanning it concludes "not receipted" about a
/// transfer that DID move the money — the one wrong answer that invites a
/// double spend.
///
/// EVERY FIELD READ HERE IS ONE WHOSE VALUE IS THE ANSWER, so a field the node
/// SENT in a shape this reader cannot read makes the answer UNREADABLE rather
/// than absent. There is no next source to fall through to: this is the single
/// authoritative statement about whether the transfer committed, and treating a
/// malformed one as "not yet" would turn a broken answer into a silent Pending
/// that eventually times out as UNKNOWN with the wrong reason attached.
/// THE EXACT-HASH LOOKUP, shared by every verb that has to know whether ITS
/// OWN turn reached the chain: `Ok(Some(row))` is the node's receipt for this
/// exact turn, `Ok(None)` is "not yet" and is never a refusal, and `Err` is a
/// shape this reader cannot read, which is UNKNOWN in both directions.
fn exact_receipt<'a>(
    want_turn_hash: &str,
    body: &'a serde_json::Value,
) -> std::result::Result<Option<&'a serde_json::Value>, String> {
    let Some(rows) = body.as_array() else {
        return Err(format!(
            "the exact-hash receipt query answered with {} instead of an array",
            json_kind(body)
        ));
    };
    if rows.is_empty() {
        return Ok(None);
    }
    if rows.len() > 1 {
        // A turn hash binds the agent and the nonce, so the chain cannot hold
        // two receipts for one hash. More than one row means the filter is not
        // the exact-match filter this reader assumes, and every conclusion
        // below it would be drawn from a row picked arbitrarily.
        return Err(format!(
            "the exact-hash receipt query answered with {} rows for one turn hash",
            rows.len()
        ));
    }
    let row = &rows[0];
    let Some(got_hash) = row.get("turn_hash").and_then(|v| v.as_str()) else {
        return Err(
            "the receipt row carries no string turn_hash, so it cannot be bound to this turn"
                .to_string(),
        );
    };
    if !got_hash.eq_ignore_ascii_case(want_turn_hash) {
        return Err(format!(
            "the exact-hash receipt query for {want_turn_hash} answered with turn {got_hash}"
        ));
    }
    Ok(Some(row))
}

fn classify_commitment(
    want_turn_hash: &str,
    body: &serde_json::Value,
    accept_tentative: bool,
) -> Commitment {
    let row = match exact_receipt(want_turn_hash, body) {
        Err(why) => return Commitment::Unreadable(why),
        Ok(None) => return Commitment::Pending,
        Ok(Some(row)) => row,
    };

    let Some(raw_finality) = row.get("finality").and_then(|v| v.as_str()) else {
        return Commitment::Unreadable(
            "the receipt row carries no string finality, so how final this transfer is is unknown"
                .to_string(),
        );
    };
    let finality = raw_finality.trim().to_ascii_lowercase();
    match finality.as_str() {
        FINALITY_FINAL => {}
        FINALITY_TENTATIVE if accept_tentative => {}
        FINALITY_TENTATIVE => return Commitment::BelowFinality { finality },
        other => {
            // A finality word this reader does not know is UNKNOWN in both
            // directions. Accepting it would let a future weaker level pass as
            // commitment; refusing it would report a stronger one as a failure.
            return Commitment::Unreadable(format!(
                "the receipt row reports finality '{other}', which this reader does not know: \
                 it is neither accepted nor refused"
            ));
        }
    }

    let Some(receipt_hash) = row.get("receipt_hash").and_then(|v| v.as_str()) else {
        return Commitment::Unreadable(
            "the receipt row carries no string receipt_hash".to_string(),
        );
    };
    if !is_hash_hex(receipt_hash) {
        return Commitment::Unreadable(format!(
            "the receipt row's receipt_hash '{receipt_hash}' is not 64 hex characters"
        ));
    }
    let Some(chain_index) = row.get("chain_index").and_then(|v| v.as_u64()) else {
        return Commitment::Unreadable(
            "the receipt row carries no unsigned chain_index".to_string(),
        );
    };

    Commitment::Committed {
        receipt_hash: receipt_hash.to_ascii_lowercase(),
        chain_index,
        finality,
    }
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

/// The `POST /api/faucet` body. It never carries `public_key`.
///
/// With `public_key`, a solo node's zero-amount arm mints a hosted cell bound
/// to the Ed25519 key and carrying no ML-DSA anchor. The node's first-turn
/// claim (`signed_turn_validation::claimed_actor_cell`) declines a cell that is
/// already the signer's, and `validate_signed_turn` refuses a hybrid turn
/// against a cell with no anchor and no enrollment as not enrolled, before it
/// reads the posture: that cell can never act (node test
/// `a_key_bound_zero_amount_cell_cannot_act_but_a_stub_takes_its_first_turn`).
/// Without it the node leaves a zero-pk stub in the default asset, and this
/// signer's first hybrid turn claims it with the envelope's own identity. A
/// funded grant lands as a stub either way. Measured on both node lines: an
/// init-minted node and a genesis-less solo node from before the claim
/// existed each commit a stub's first send.
fn faucet_request(cell_hex: &str, amount: u64) -> serde_json::Value {
    serde_json::json!({ "recipient": cell_hex, "amount": amount })
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
        .json(&faucet_request(cell_hex, shortfall))
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
    amount: Option<u64>,
    accept_tentative: bool,
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
        amount: None,
        accept_tentative: false,
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
            "--amount" => {
                f.amount = Some(
                    val("--amount")?
                        .parse()
                        .map_err(|e| err(format!("--amount must be a u64: {e}")))?,
                )
            }
            "--accept-tentative" => f.accept_tentative = true,
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
       rides in the signed turn (memo + event data words)\n\
  transfer --to CELL_HEX --amount N [--profile P] [--node-url U] [--token T]\n\
           [--fund N] [--accept-tentative]\n\
       move N computrons from the profile's own cell to another cell. Exit 0 only\n\
       when a receipt for EXACTLY this turn hash is on the node's chain; the\n\
       printed `committed` is true only then. A solo-mode devnet marks every\n\
       receipt `tentative`, so accepting that level needs --accept-tentative\n\n\
env (flags win): DREGG_NODE_URL, DREGG_API_TOKEN (or DREGG_NODE_PASSPHRASE\n\
to unlock), DREGG_PROFILE (the SDK's active-profile convention)";

async fn cmd_join(f: Flags) -> Result<()> {
    let http = reqwest::Client::new();
    let (name, clerk) = resolve_clerk(f.profile.as_deref(), true)?;
    let cell_hex = hex::encode(clerk.cell_id("default").as_bytes());
    let pk_hex = hex::encode(clerk.public_key().0);

    // COORDINATION-EXEMPT JOIN: when the deployment opts into the coordination
    // class (DREGG_COORDINATION_EXEMPT truthy — helm's `cell.coord_fee()==0`
    // forwards the env), materializing the cell requires the amount=0 path
    // (cell creation, free) and NEVER a faucet-funded grant. A faucet grant
    // bricks the nonce on devnet after ~1 successful call and drains the cell
    // on every failed retry — an exempt join that still routes through the
    // faucet is the whole reason every seat has been DEGRADED|join_failed
    // since the fleet reboot. The signer's own docs promised this class was
    // free four months before any deployment turned it on.
    //
    // Non-exempt join is unchanged: `--fund N` (default 5000) calls the faucet.
    // BOTH BOUNDS GO TO ZERO, not just the minimum. `ensure_cell` computes
    // `funding_shortfall(initial, minimum_balance, target_balance)` and only
    // returns early on `!materialized && shortfall == 0`. An ABSENT cell is
    // `materialized`, so it always POSTs — with `amount: shortfall`, derived
    // from TARGET. Leaving target at `f.fund` therefore still requested a
    // FUNDED grant on the exact path an exempt join must never take: first
    // join, cell does not exist yet. Measured live 2026-07-28 — the exempt
    // banner printed and the very next line was
    // `faucet refused funding: ... Ed25519 (classical) signature half failed`.
    //
    // With both at 0 the shortfall is 0, so the POST carries amount=0: the
    // free materialization path, which returns success before any Transfer is
    // built and needs no faucet signature at all.
    let costs = fee_cost_model();
    let (minimum_balance, target_balance) = if costs.coordination_exempt {
        eprintln!("[client-sign] coordination-exempt join — materializing cell {cell_hex} (free, no faucet grant)");
        (0u64, 0u64)
    } else {
        (f.fund, f.fund)
    };
    let funding = ensure_cell(
        &http,
        &f.node_url,
        &cell_hex,
        minimum_balance,
        target_balance,
    )
    .await?;
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
    let presence = ensure_cell(&http, &f.node_url, &cell_hex, 0, 0).await?;

    let federation_id = node
        .fetch_executor_federation_id()
        .await
        .map_err(|e| err(format!("fetch executor federation id: {e}")))?;
    // The fee depends on neither the nonce nor any signature byte (see
    // `chat_fee`), so it is sized here without signing. The one signed build
    // happens below, at the nonce fetched after funding.
    let fee = chat_fee(&clerk, fee_cost_model(), cell, &f.topic, &payload);

    // Funding is SEND correctness, not a one-time join convenience. One grant
    // reserves a bounded six-send burst inside the faucet's 60-second window;
    // cap the requested delta to the node's 10,000-computron per-request law.
    let desired = f.fund.max(fee.saturating_mul(SEND_FUNDING_HORIZON));
    let target = desired.min(presence.balance.saturating_add(FAUCET_MAX_GRANT));
    if target < fee {
        return Err(err(format!(
            "turn fee {} exceeds the current balance {} plus the faucet's {}-computron grant cap",
            fee, presence.balance, FAUCET_MAX_GRANT
        )));
    }
    let funding = ensure_cell(&http, &f.node_url, &cell_hex, fee, target).await?;

    // Funding can wait up to 10s and another same-profile sender can commit in
    // that window. Fetch the nonce immediately before signing, because
    // dregg-action-sig-v3 binds it.
    let nonce = node
        .fetch_cell_nonce(&cell)
        .await
        .map_err(|e| err(format!("fetch own-cell nonce after funding: {e}")))?;
    let mut turn = build_chat_turn(&clerk, cell, &f.topic, &payload, &federation_id, nonce);
    turn.fee = TurnExecutor::new(fee_cost_model()).estimate_cost(&turn);
    if turn.fee > funding.balance {
        return Err(err(format!(
            "final turn fee {} exceeds the observed funded balance {}",
            turn.fee, funding.balance
        )));
    }
    // THE AGENT'S OWN RECEIPT HEAD, not the node-wide tip. A node that keeps
    // a head per agent admits a signed turn only when `previous_receipt_hash`
    // equals the head of THIS agent's chain, and the node-wide tip is another
    // seat's receipt whenever another seat committed since, so threading it is
    // refused with "receipt chain mismatch" (see
    // `NodeHttpClient::fetch_agent_receipt_head`). An older solo node wants the
    // node-wide tip instead; `submit_turn` retries once on it.
    turn.previous_receipt_hash = node
        .fetch_agent_receipt_head(&cell)
        .await
        .map_err(|e| err(format!("fetch own-cell receipt head after funding: {e}")))?;
    let bearer = ensure_token(&http, &f.node_url, f.token.clone()).await?;

    // THE OPERATION'S IDENTITY IS COMPUTED FROM THE TURN THIS PROCESS SIGNED,
    // inside `submit_turn`, and never taken from the answer — the same rule the
    // transfer verb follows, applied to its sibling.
    //
    // WIDENING THE LOOKUP IS WHAT MADE THIS URGENT. Binding to the hash the
    // SERVER reported was always a trust defect, and the old fifty-receipt
    // window hid most of it: a response naming some historical turn B could
    // not be confirmed, because B's receipt had long since fallen out of that
    // window. Searching the WHOLE chain finds B, so the same wrong answer now
    // prints `sent: true` beside THIS turn's topic and payload. A cure for one
    // defect made another reachable, which is the cost of fixing an instance
    // and leaving its sibling.
    let Submitted { turn_hash, answer } = submit_turn(
        &http,
        &node,
        &f.node_url,
        &bearer,
        &clerk,
        &mut turn,
        "send",
    )
    .await?;
    match answer {
        Err(why) => return Err(err(why)),
        Ok(Admission::Took) => {}
        Ok(Admission::Refused(why)) => {
            return Err(err(format!("node refused the turn: {why}")));
        }
        Ok(Admission::Unknown(why)) => {
            return Err(err(format!(
                "{why}. This is UNKNOWN, not a refusal: the turn may have \
                 committed. Re-read the node with \
                 `curl '{}/api/starbridge/receipts?limit=2&turn_hash={turn_hash}'` \
                 and decide from that.",
                f.node_url
            )));
        }
    }
    eprintln!("[client-sign] turn accepted: {turn_hash}; awaiting receipt...");

    // Receipt resolution across the consensus-finality window (~2s typical).
    // Fail-closed after 30s: exit 0 means RECEIPTED, never merely accepted.
    //
    // THE LOOKUP IS BY EXACT TURN HASH OVER THE WHOLE CHAIN. Scanning
    // `/api/receipts` could not answer this question: that route serves only
    // the newest fifty receipts, so once fifty land inside the thirty-second
    // window the receipt for this send is no longer in the response and the
    // client reports a turn that DID commit as unreceipted. The exact-hash
    // query filters the whole chain, and an answer it cannot read is UNKNOWN
    // rather than a silent "not yet" that times out with the wrong reason.
    //
    // FINALITY IS REPORTED, NOT DECIDED, which is this verb's existing
    // contract and is deliberately unchanged: a solo-mode node marks every
    // committed receipt tentative, and an EmitEvent moves no balance.
    let confirm_url = format!(
        "{}/api/starbridge/receipts?limit=2&turn_hash={turn_hash}",
        f.node_url
    );
    for _ in 0..120 {
        let receipts = get_json(&http, &confirm_url).await?;
        let found = exact_receipt(&turn_hash, &receipts).map_err(|why| {
            err(format!(
                "cannot tell whether turn {turn_hash} was receipted: {why}. \
                 This is UNKNOWN, not a refusal."
            ))
        })?;
        if let Some(r) = found {
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


/// `transfer` — move computrons from the profile's own cell to another cell.
///
/// The signer is the SOURCE. `Effect::Transfer { from: own cell, to, amount }`
/// rides an action whose target is that same cell, so the executor's
/// permission check gates the withdrawal on `Send` over the signed action, and
/// the destination is gated on its own `Receive`. Nothing here asserts the
/// authority; the signature is presented and the owning layer decides.
///
/// NOT COORDINATION-EXEMPT, unlike `send`. `Turn::is_coordination` requires
/// every effect to be an `EmitEvent` and no `balance_change`, so a Transfer
/// leaves the class whatever `DREGG_COORDINATION_EXEMPT` says, and
/// `estimate_cost` returns the real computron cost. The source must therefore
/// hold `amount + fee`, not `amount`.
async fn cmd_transfer(f: Flags) -> Result<()> {
    let amount = f
        .amount
        .ok_or_else(|| err("transfer requires --amount N (computrons)".to_string()))?;
    if amount == 0 {
        return Err(err(
            "transfer requires a positive --amount: a zero transfer moves nothing \
             and still burns the turn fee"
                .to_string(),
        ));
    }
    let to_flag = f
        .to
        .clone()
        .ok_or_else(|| err("transfer requires --to CELL_HEX".to_string()))?;

    let http = reqwest::Client::new();
    let node = NodeHttpClient::new(&f.node_url);
    let (name, clerk) = resolve_clerk(f.profile.as_deref(), false)?;
    let from = clerk.cell_id("default");
    let from_hex = hex::encode(from.as_bytes());
    let to_hex = resolve_destination(&to_flag, &from_hex, &name)?;
    let to = parse_cell_hex("--to", &to_hex)?;

    // Materialize the source without consuming the funded faucet bucket, the
    // same zero-amount path `send` opens with.
    let presence = ensure_cell(&http, &f.node_url, &from_hex, 0, 0).await?;

    let federation_id = node
        .fetch_executor_federation_id()
        .await
        .map_err(|e| err(format!("fetch executor federation id: {e}")))?;
    let estimate_nonce = node
        .fetch_cell_nonce(&from)
        .await
        .map_err(|e| err(format!("fetch own-cell nonce for fee estimate: {e}")))?;
    let mut turn = build_transfer_turn(
        &clerk,
        from,
        to,
        amount,
        &federation_id,
        estimate_nonce,
    );
    turn.fee = TurnExecutor::new(fee_cost_model()).estimate_cost(&turn);

    // The source must cover the MOVED VALUE AND the fee. `send`'s funding math
    // covers the fee alone because an EmitEvent moves nothing.
    let needed = amount.checked_add(turn.fee).ok_or_else(|| {
        err(format!(
            "amount {amount} plus fee {} overflows u64",
            turn.fee
        ))
    })?;
    let desired = f.fund.max(needed);
    let target = desired.min(presence.balance.saturating_add(FAUCET_MAX_GRANT));
    if target < needed {
        return Err(err(format!(
            "transfer of {amount} plus fee {} needs {needed} computrons; the source holds {} \
             and the faucet grants at most {FAUCET_MAX_GRANT} per request",
            turn.fee, presence.balance
        )));
    }
    let funding = ensure_cell(&http, &f.node_url, &from_hex, needed, target).await?;

    // Funding can wait up to 10s and another sender on this profile can commit
    // in that window. Refetch the nonce immediately before signing, then
    // rebuild: `dregg-action-sig-v3` binds the nonce.
    let nonce = node
        .fetch_cell_nonce(&from)
        .await
        .map_err(|e| err(format!("refetch own-cell nonce after funding: {e}")))?;
    turn = build_transfer_turn(&clerk, from, to, amount, &federation_id, nonce);
    turn.fee = TurnExecutor::new(fee_cost_model()).estimate_cost(&turn);
    let needed = amount.checked_add(turn.fee).ok_or_else(|| {
        err(format!(
            "amount {amount} plus fee {} overflows u64",
            turn.fee
        ))
    })?;
    if needed > funding.balance {
        return Err(err(format!(
            "final transfer of {amount} plus fee {} exceeds the observed funded balance {}",
            turn.fee, funding.balance
        )));
    }
    // The source's OWN receipt head, and the one retry on the node-wide head,
    // for the reasons `cmd_send` and `submit_turn` give.
    turn.previous_receipt_hash = node
        .fetch_agent_receipt_head(&from)
        .await
        .map_err(|e| err(format!("fetch source-cell receipt head after funding: {e}")))?;
    let bearer = ensure_token(&http, &f.node_url, f.token.clone()).await?;

    // THE OPERATION'S IDENTITY IS COMPUTED FROM THE TURN THIS PROCESS SIGNED,
    // inside `submit_turn`, and never taken from the answer. `Turn::hash`
    // absorbs the call forest, which absorbs this Transfer's from, to and
    // amount, so this hex IS this transfer. Confirming against a hash the
    // SERVER chose would let a faulty or hostile answer point the confirmation
    // at some other committed turn and have its receipt printed beside THIS
    // transfer's recipient and amount — a wrong-operation success, which is the
    // one outcome a value mover must never produce. After a retry it is the
    // RETRIED turn's hash: the first was refused, so it moved nothing.
    let Submitted { turn_hash, answer } = submit_turn(
        &http,
        &node,
        &f.node_url,
        &bearer,
        &clerk,
        &mut turn,
        "transfer",
    )
    .await?;
    let confirm_url = format!(
        "{}/api/starbridge/receipts?limit=2&turn_hash={turn_hash}",
        f.node_url
    );
    // THE LOCAL HASH IS WHAT THE RESPONSE IS CHECKED AGAINST, never the other
    // way round. `submit_turn` is the only place the submit answer is read.
    match answer {
        Ok(Admission::Took) => {}
        Ok(Admission::Refused(why)) => {
            return Err(err(format!("node refused the transfer: {why}")));
        }
        Ok(Admission::Unknown(why)) | Err(why) => {
            return Err(unknown_after_submit(why, amount, &confirm_url));
        }
    }
    eprintln!("[client-sign] transfer admitted: {turn_hash}; confirming commitment...");

    // COMMITMENT IS CONFIRMED AGAINST THE CHAIN, BY EXACT HASH. Only a commit
    // appends a receipt, and the turn hash binds this transfer's source,
    // destination and amount, so a receipt at this hash is the node's own
    // statement that THIS transfer moved. The exact-hash query filters the
    // whole chain; `/api/receipts` serves only the newest 50 and would report
    // a committed transfer as unreceipted on a busy node.
    let mut last_below: Option<String> = None;
    for _ in 0..120 {
        let body = get_json(&http, &confirm_url).await.map_err(|e| {
            unknown_after_submit(format!("{e}"), amount, &confirm_url)
        })?;
        match classify_commitment(&turn_hash, &body, f.accept_tentative) {
            Commitment::Committed {
                receipt_hash,
                chain_index,
                finality,
            } => {
                println!(
                    "{}",
                    serde_json::json!({
                        "transferred": true,
                        "committed": true,
                        "node": f.node_url,
                        "profile": name,
                        "from": from_hex,
                        "to": to_hex,
                        "amount": amount,
                        "fee": turn.fee,
                        "materialized": presence.materialized,
                        "topped_up": funding.topped_up,
                        "joined_in_flight": funding.joined_in_flight,
                        "balance_before_transfer": funding.balance,
                        "turn_hash": turn_hash,
                        "receipt_hash": receipt_hash,
                        "chain_index": chain_index,
                        "finality": finality,
                        "finality_required": if f.accept_tentative {
                            "tentative-or-final"
                        } else {
                            FINALITY_FINAL
                        },
                    })
                );
                return Ok(());
            }
            Commitment::Pending => {}
            Commitment::BelowFinality { finality } => last_below = Some(finality),
            Commitment::Unreadable(why) => {
                return Err(unknown_after_submit(
                    format!("cannot tell whether transfer {turn_hash} \
                             committed: {why}"),
                    amount, &confirm_url));
            }
        }
        tokio::time::sleep(std::time::Duration::from_millis(250)).await;
    }
    let seen = match last_below {
        Some(finality) => format!(
            " A receipt for it IS on the chain at finality '{finality}', below the \
             level this call required"
        ),
        None => String::new(),
    };
    Err(unknown_after_submit(
        format!("transfer {turn_hash} was admitted but not confirmed committed \
                 within 30s.{seen}"),
        amount, &confirm_url))
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
    // THE KEYGEN CORE IS INSTALLED TOO, because `join` CREATES an identity on
    // first use and that is a keygen. Without it the audit gate aborts the
    // process with SIGABRT on exactly the documented first-use path: a brand
    // new profile could never be made by this binary, and the failure is a
    // signal rather than an error anyone could act on.
    let keygen_core = dregg_sdk::install_verified_mldsa_keygen_core_real();
    eprintln!(
        "[client-sign] verified ML-DSA cores: sign {sign_core:?}, verify \
         {verify_core:?}, keygen {keygen_core:?}"
    );

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
            "transfer" => cmd_transfer(flags).await,
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

    fn exempt_costs() -> ComputronCosts {
        let mut costs = ComputronCosts::default();
        costs.coordination_exempt = true;
        costs
    }

    /// The unsigned estimate must equal the fee of the REALLY signed turn, for
    /// both cost models, several payload sizes and any nonce. This is the
    /// equality that lets `cmd_send` skip the estimate-only signature.
    #[test]
    fn unsigned_fee_estimate_equals_the_signed_turns_fee() {
        let clerk = AgentCipherclerk::from_seed([7u8; 64]);
        let cell = clerk.cell_id("default");
        let federation_id = [9u8; 32];
        let long = "x".repeat(1_000);
        for costs in [ComputronCosts::default(), exempt_costs()] {
            for payload in ["", "hi", "a chat-sized payload of some words", long.as_str()] {
                let fee = chat_fee(&clerk, costs.clone(), cell, "helm.chat", payload);
                for nonce in [0u64, 1, 41] {
                    let signed =
                        build_chat_turn(&clerk, cell, "helm.chat", payload, &federation_id, nonce);
                    assert!(matches!(
                        signed.call_forest.roots[0].action.authorization,
                        Authorization::HybridSignature { .. }
                    ));
                    assert_eq!(
                        fee,
                        TurnExecutor::new(costs.clone()).estimate_cost(&signed),
                        "exempt={} payload_len={} nonce={nonce}",
                        costs.coordination_exempt,
                        payload.len()
                    );
                }
            }
        }
        let paid = chat_fee(&clerk, ComputronCosts::default(), cell, "helm.chat", "hi");
        assert!(paid > 0, "the non-exempt fee must stay a real fee");
        assert_eq!(chat_fee(&clerk, exempt_costs(), cell, "helm.chat", "hi"), 0);
    }

    /// For a fixed key, federation, nonce and payload, the turn the new flow
    /// signs and submits is byte-identical to the one the old flow (sign once
    /// to estimate, then rebuild and sign again) signed and submitted.
    #[test]
    fn one_signed_build_is_byte_identical_to_the_old_estimate_then_rebuild_flow() {
        let clerk = AgentCipherclerk::from_seed([3u8; 64]);
        let cell = clerk.cell_id("default");
        let federation_id = [5u8; 32];
        let payload = "the same chat post under both flows";
        let (estimate_nonce, nonce) = (11u64, 12u64); // another sender raced in between
        let costs = ComputronCosts::default();
        let head = Some([4u8; 32]);

        // OLD: sign at the estimate nonce, estimate, then rebuild at the fresh nonce.
        let mut old = build_chat_turn(&clerk, cell, "helm.chat", payload, &federation_id, estimate_nonce);
        old.fee = TurnExecutor::new(costs.clone()).estimate_cost(&old);
        let old_funding_fee = old.fee;
        old = build_chat_turn(&clerk, cell, "helm.chat", payload, &federation_id, nonce);
        old.fee = TurnExecutor::new(costs.clone()).estimate_cost(&old);
        old.previous_receipt_hash = head;
        let old_signed = postcard::to_stdvec(&clerk.sign_turn(&old)).unwrap();

        // NEW: unsigned estimate, then the one signed build at the fresh nonce.
        let new_funding_fee = chat_fee(&clerk, costs.clone(), cell, "helm.chat", payload);
        let mut new = build_chat_turn(&clerk, cell, "helm.chat", payload, &federation_id, nonce);
        new.fee = TurnExecutor::new(costs).estimate_cost(&new);
        new.previous_receipt_hash = head;
        let new_signed = postcard::to_stdvec(&clerk.sign_turn(&new)).unwrap();

        assert_eq!(old_funding_fee, new_funding_fee, "funding is sized identically");
        assert_eq!(old_signed, new_signed, "the submitted SignedTurn bytes are identical");
        assert_eq!(new.nonce, nonce);
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
        let (cell_hex, recipient) = {
            let node = state.lock().await;
            (hex::encode(node.recipient.0), node.recipient)
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
        let outcome = ensure_cell(&http, &url, &cell_hex, 1_510, 9_060)
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

    /// The body carries no `public_key` at any amount: a key in it makes the
    /// dead key-bound cell on a solo node (see [`faucet_request`]).
    #[test]
    fn a_stub_materialization_carries_no_public_key() {
        let cell = "ab".repeat(32);
        for amount in [0, 5_000] {
            let body = faucet_request(&cell, amount);
            assert_eq!(
                body,
                serde_json::json!({ "recipient": cell, "amount": amount })
            );
        }
    }

    /// THE WIRING, against a real-executor node: whatever the node lists on
    /// `/api/federations` (no committee, or a configured one), the
    /// materialization `ensure_cell` sends it carries no `public_key`, and the
    /// cell the node is left holding is the zero-pk stub a first turn claims.
    /// `TestNode` mints the key-bound hosted cell when a key arrives, as a solo
    /// node does, so a key that reaches the wire fails the stub assertion too.
    #[cfg(feature = "test-support")]
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn every_node_shape_receives_a_keyless_materialization() {
        use dregg_sdk_net::test_support::TestNode;

        let clerk = AgentCipherclerk::from_seed([0x5A; 64]);
        let cell = clerk.cell_id("default");
        let cell_hex = hex::encode(cell.as_bytes());
        for configured in [false, true] {
            let (node, _agent) = TestNode::genesis([0x11; 32], [0x22; 32], 0);
            let node = if configured {
                node.with_configured_committee([0x33; 32])
            } else {
                node
            };
            let spawned = node.spawn().await;
            let http = reqwest::Client::new();
            let outcome = ensure_cell(&http, spawned.base_url(), &cell_hex, 0, 0)
                .await
                .expect("materialize");
            assert!(outcome.materialized, "configured={configured}");
            let node = spawned.lock().await;
            assert_eq!(
                node.faucet_requests(),
                [serde_json::json!({ "recipient": cell_hex, "amount": 0 })],
                "configured={configured}: the node must receive exactly one keyless request"
            );
            assert_eq!(
                node.ledger().get(&cell).map(|c| *c.public_key()),
                Some([0u8; 32]),
                "configured={configured}: the node must hold a claimable zero-pk stub"
            );
        }
    }

    #[tokio::test]
    async fn rate_limited_duplicate_joins_in_flight_grant() {
        let (url, state, handle) = spawn_faucet_node(90, FaucetMode::RateLimitedThenCommit).await;
        let cell_hex = hex::encode(state.lock().await.recipient.0);
        let outcome = ensure_cell(&reqwest::Client::new(), &url, &cell_hex, 1_510, 9_060)
            .await
            .expect("duplicate owner must join the in-flight grant");
        assert!(outcome.joined_in_flight);
        assert_eq!(outcome.balance, 9_060);
        assert_eq!(state.lock().await.calls, 1);
        handle.abort();
    }

    // ── transfer: admission is not commitment ───────────────────────────────
    //
    // Every arm here drives `classify_commitment`, the one door `cmd_transfer`
    // asks "did THIS transfer commit?" through. They need no node: the fixtures
    // are the exact JSON shapes `GET /api/starbridge/receipts?turn_hash=..`
    // serves, whose fields come from `ReceiptInfo` with `#[serde(flatten)]`.

    const WANT: &str = "aa11bb22cc33dd44ee55ff6600778899aabbccddeeff00112233445566778899";
    const OTHER: &str = "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff";
    const RECEIPT: &str = "1111111111111111111111111111111111111111111111111111111111111111";

    fn row(turn_hash: &str, finality: &str) -> serde_json::Value {
        serde_json::json!({
            "chain_index": 7,
            "chain_head": true,
            "receipt_hash": RECEIPT,
            "turn_hash": turn_hash,
            "agent": OTHER,
            "finality": finality,
            "effects_hash": RECEIPT,
        })
    }

    #[test]
    fn an_exact_receipt_at_final_is_the_commitment() {
        // UNCONDITIONAL POSITIVE, first: every refusal below must be a refusal
        // of something, not the behaviour of a reader that never says yes.
        assert_eq!(
            classify_commitment(WANT, &serde_json::json!([row(WANT, "final")]), false),
            Commitment::Committed {
                receipt_hash: RECEIPT.to_string(),
                chain_index: 7,
                finality: "final".to_string(),
            }
        );
    }

    #[test]
    fn an_admitted_turn_hash_with_no_receipt_is_never_commitment() {
        // The pole the whole verb exists for: the node handed back a turn hash
        // and nothing has committed. Pending, and Pending is not success.
        assert_eq!(
            classify_commitment(WANT, &serde_json::json!([]), true),
            Commitment::Pending
        );
    }

    #[test]
    fn a_tentative_receipt_commits_only_when_the_caller_accepted_that_level() {
        // Both directions in one arm, because the difference between them is
        // the caller's decision and nothing else about the input changes.
        assert_eq!(
            classify_commitment(WANT, &serde_json::json!([row(WANT, "tentative")]), false),
            Commitment::BelowFinality {
                finality: "tentative".to_string()
            }
        );
        assert_eq!(
            classify_commitment(WANT, &serde_json::json!([row(WANT, "tentative")]), true),
            Commitment::Committed {
                receipt_hash: RECEIPT.to_string(),
                chain_index: 7,
                finality: "tentative".to_string(),
            }
        );
    }

    #[test]
    fn a_receipt_for_another_turn_is_unreadable_not_pending() {
        // An exact-hash query that answers about a DIFFERENT turn is a broken
        // filter. Skipping the row would silently downgrade this reader to
        // "nothing committed yet" on a node that is not answering the question.
        let got = classify_commitment(WANT, &serde_json::json!([row(OTHER, "final")]), true);
        assert!(
            matches!(&got, Commitment::Unreadable(why) if why.contains(OTHER)),
            "{got:?}"
        );
    }

    #[test]
    fn a_finality_word_this_reader_does_not_know_is_unreadable_in_both_directions() {
        for word in ["provisional", "", "FINALIZED"] {
            let got = classify_commitment(WANT, &serde_json::json!([row(WANT, word)]), true);
            assert!(
                matches!(got, Commitment::Unreadable(_)),
                "finality '{word}' must be UNKNOWN, got {got:?}"
            );
        }
    }

    #[test]
    fn finality_is_read_case_and_space_insensitively() {
        assert_eq!(
            classify_commitment(WANT, &serde_json::json!([row(WANT, " Final ")]), false),
            Commitment::Committed {
                receipt_hash: RECEIPT.to_string(),
                chain_index: 7,
                finality: "final".to_string(),
            }
        );
    }

    #[test]
    fn an_uppercase_turn_hash_still_binds_to_this_transfer() {
        assert_eq!(
            classify_commitment(
                WANT,
                &serde_json::json!([row(&WANT.to_uppercase(), "final")]),
                false
            ),
            Commitment::Committed {
                receipt_hash: RECEIPT.to_string(),
                chain_index: 7,
                finality: "final".to_string(),
            }
        );
    }

    #[test]
    fn a_field_whose_value_is_the_answer_is_unreadable_when_malformed() {
        // Each of these is a field the node SENT in a shape this reader cannot
        // read, at a site with no next source to fall through to. Absent and
        // malformed are the same verdict here — UNKNOWN — and neither is
        // commitment.
        let cases: Vec<serde_json::Value> = vec![
            serde_json::json!([{"receipt_hash": RECEIPT, "chain_index": 7, "finality": "final"}]),
            serde_json::json!([{"turn_hash": 12, "receipt_hash": RECEIPT, "chain_index": 7, "finality": "final"}]),
            serde_json::json!([{"turn_hash": WANT, "receipt_hash": RECEIPT, "chain_index": 7}]),
            serde_json::json!([{"turn_hash": WANT, "receipt_hash": RECEIPT, "chain_index": 7, "finality": false}]),
            serde_json::json!([{"turn_hash": WANT, "chain_index": 7, "finality": "final"}]),
            serde_json::json!([{"turn_hash": WANT, "receipt_hash": "zz", "chain_index": 7, "finality": "final"}]),
            serde_json::json!([{"turn_hash": WANT, "receipt_hash": 1, "chain_index": 7, "finality": "final"}]),
            serde_json::json!([{"turn_hash": WANT, "receipt_hash": RECEIPT, "finality": "final"}]),
            serde_json::json!([{"turn_hash": WANT, "receipt_hash": RECEIPT, "chain_index": -1, "finality": "final"}]),
        ];
        for body in cases {
            let got = classify_commitment(WANT, &body, true);
            assert!(
                matches!(got, Commitment::Unreadable(_)),
                "{body} must be UNREADABLE, got {got:?}"
            );
        }
    }

    #[test]
    fn a_body_that_is_not_an_array_is_unreadable() {
        for body in [
            serde_json::json!({"error": "not found"}),
            serde_json::json!(null),
            serde_json::json!("[]"),
        ] {
            let got = classify_commitment(WANT, &body, true);
            assert!(
                matches!(got, Commitment::Unreadable(_)),
                "{body} must be UNREADABLE, got {got:?}"
            );
        }
    }

    #[test]
    fn two_rows_for_one_exact_hash_is_unreadable() {
        // A turn hash binds the agent and the nonce, so the chain cannot hold
        // two receipts for one. Taking the first would pick arbitrarily.
        let got = classify_commitment(
            WANT,
            &serde_json::json!([row(WANT, "final"), row(WANT, "final")]),
            true,
        );
        assert!(matches!(got, Commitment::Unreadable(_)), "{got:?}");
    }

    // ── transfer: the destination refusals ──────────────────────────────────

    #[test]
    fn a_destination_that_is_not_the_signers_own_cell_is_accepted() {
        assert_eq!(
            resolve_destination(&OTHER.to_uppercase(), WANT, "p").unwrap(),
            OTHER
        );
    }

    #[test]
    fn a_transfer_to_the_signers_own_cell_is_refused() {
        // `send`'s guard is the opposite shape and this is not its inverse:
        // both refuse a caller mistake, and neither decides authority.
        let e = resolve_destination(&WANT.to_uppercase(), WANT, "seat")
            .expect_err("a self-transfer must be refused");
        assert!(e.to_string().contains("own cell"), "{e}");
    }

    #[test]
    fn a_destination_that_is_not_a_32_byte_cell_is_refused() {
        for bad in ["", "aa", "nothex", &WANT[..62], &format!("{WANT}aa")] {
            assert!(
                resolve_destination(bad, OTHER, "seat").is_err(),
                "'{bad}' must be refused as a cell id"
            );
        }
    }

    // ── the exact-hash lookup `send` and `transfer` now share ───────────────
    //
    // `send` used to scan `GET /api/receipts`, which serves only the newest
    // FIFTY receipts, so a busy node pushed its own receipt out of the window
    // and the client reported a committed turn as unreceipted. That cap is the
    // NODE's (`receipt_infos_from_chain(&s, 50)`) and cannot be exercised from
    // this crate; what IS pinned here is the reader that replaced the scan.

    #[test]
    fn the_exact_receipt_for_this_turn_is_returned() {
        let body = serde_json::json!([row(WANT, "tentative")]);
        let got = exact_receipt(WANT, &body).expect("readable");
        assert_eq!(
            got.and_then(|r| r.get("turn_hash")).and_then(|v| v.as_str()),
            Some(WANT)
        );
    }

    #[test]
    fn no_receipt_yet_is_not_an_error() {
        // The distinction the whole poll depends on: "not yet" must keep
        // waiting, and only a shape the reader cannot read may abort it.
        assert_eq!(exact_receipt(WANT, &serde_json::json!([])), Ok(None));
    }

    #[test]
    fn an_uppercase_turn_hash_is_still_this_turn() {
        let body = serde_json::json!([row(&WANT.to_uppercase(), "final")]);
        assert!(exact_receipt(WANT, &body).expect("readable").is_some());
    }

    #[test]
    fn an_unreadable_answer_is_an_error_and_never_not_yet() {
        // Each of these used to be indistinguishable from "no receipt yet",
        // which is how a broken answer became a thirty-second wait that ended
        // with the wrong reason attached.
        let cases: Vec<serde_json::Value> = vec![
            serde_json::json!([row(OTHER, "final")]),
            serde_json::json!([row(WANT, "final"), row(WANT, "final")]),
            serde_json::json!({"error": "not found"}),
            serde_json::json!(null),
            serde_json::json!([{"receipt_hash": RECEIPT, "finality": "final"}]),
            serde_json::json!([{"turn_hash": 12, "finality": "final"}]),
        ];
        for body in cases {
            assert!(
                exact_receipt(WANT, &body).is_err(),
                "{body} must be UNREADABLE, not Ok"
            );
        }
    }

    #[test]
    fn send_binds_its_confirmation_to_the_turn_IT_signed() {
        // THE DEFECT WIDENING THE LOOKUP MADE REACHABLE. Binding to the hash
        // the SERVER reported was always wrong; the old fifty-receipt window
        // hid most of it, because a response naming a HISTORICAL turn could
        // not be confirmed once that turn's receipt fell out of the window.
        // Searching the whole chain finds it, so the same wrong answer would
        // print success beside this turn's own topic and payload.
        //
        // `send` and `transfer` now ask the same question through the same
        // reader, so the sibling cannot drift from the cure again.
        assert_eq!(
            bind_admission("transfer", WANT, &serde_json::json!({
                "accepted": true, "turn_hash": WANT
            })),
            Admission::Took
        );
        let got = bind_admission("transfer", WANT, &serde_json::json!({
            "accepted": true, "turn_hash": OTHER
        }));
        assert!(
            matches!(&got, Admission::Unknown(why)
                     if why.contains("is not the transfer this process signed")),
            "a historical or foreign turn hash must never confirm this send: {got:?}"
        );
        // And the receipt for that other turn is perfectly valid on its own,
        // which is exactly why the binding has to happen before the lookup.
        let body = serde_json::json!([row(OTHER, "tentative")]);
        assert!(exact_receipt(OTHER, &body).expect("readable").is_some());
        assert!(exact_receipt(WANT, &body).is_err(),
                "asking for THIS turn must not be answered by that one");
    }

    #[test]
    fn the_reason_names_what_this_caller_signed() {
        // ONE READER SERVING TWO VERBS MUST NOT NAME ONLY ONE OF THEM. The
        // reason reaches the operator, and telling someone who ran `send`
        // that their TRANSFER was not bound describes an operation that did
        // not happen — a false lead at exactly the moment they are deciding
        // whether value moved.
        for (submitted, other) in [("send", "transfer"), ("transfer", "send")] {
            let foreign = bind_admission(submitted, WANT, &serde_json::json!({
                "accepted": true, "turn_hash": OTHER
            }));
            let hashless = bind_admission(submitted, WANT, &serde_json::json!({
                "accepted": true
            }));
            for got in [&foreign, &hashless] {
                let why = match got {
                    Admission::Unknown(why) => why,
                    _ => panic!("expected UNKNOWN, got {got:?}"),
                };
                assert!(why.contains(submitted),
                        "the reason must name what THIS caller signed: {why}");
                assert!(!why.contains(other),
                        "and must not name the other verb: {why}");
            }
        }
    }

    #[test]
    fn send_does_not_gate_on_finality_the_way_transfer_does() {
        // THE DELIBERATE ASYMMETRY, pinned so nobody "unifies" it later. An
        // EmitEvent moves no balance and a solo-mode node marks every receipt
        // tentative, so `send` reports finality and does not decide on it,
        // while `transfer` refuses tentative unless the caller asked for it.
        let tentative = serde_json::json!([row(WANT, "tentative")]);
        assert!(exact_receipt(WANT, &tentative).expect("readable").is_some());
        assert_eq!(
            classify_commitment(WANT, &tentative, false),
            Commitment::BelowFinality {
                finality: "tentative".to_string()
            }
        );
    }

    // ── the submit answer is bound to the hash THIS process signed ─────────

    #[test]
    fn the_node_taking_THIS_turn_is_admission() {
        // UNCONDITIONAL POSITIVE FIRST, and note what it is NOT: taking the
        // turn is the node saying it received it. Commitment is a receipt.
        assert_eq!(
            bind_admission("transfer", WANT, &serde_json::json!({
                "accepted": true, "turn_hash": WANT
            })),
            Admission::Took
        );
        assert_eq!(
            bind_admission("transfer", WANT, &serde_json::json!({
                "accepted": true, "turn_hash": WANT.to_uppercase()
            })),
            Admission::Took
        );
    }

    #[test]
    fn a_node_naming_ANOTHER_turn_is_UNKNOWN_never_admission() {
        // THE WRONG-OPERATION SUCCESS, at the line that decides it. Confirming
        // the hash the RESPONSE chose would find that other turn's perfectly
        // valid receipt and print it beside this transfer's amount.
        let got = bind_admission("transfer", WANT, &serde_json::json!({
            "accepted": true, "turn_hash": OTHER
        }));
        assert!(
            matches!(&got, Admission::Unknown(why)
                     if why.contains("is not the transfer this process signed")),
            "{got:?}"
        );
    }

    #[test]
    fn an_accepted_answer_with_no_binding_hash_is_UNKNOWN() {
        for verdict in [
            serde_json::json!({"accepted": true}),
            serde_json::json!({"accepted": true, "turn_hash": 12}),
            serde_json::json!({"accepted": true, "turn_hash": serde_json::Value::Null}),
        ] {
            assert!(
                matches!(bind_admission("transfer", WANT, &verdict), Admission::Unknown(_)),
                "{verdict} must be UNKNOWN"
            );
        }
    }

    #[test]
    fn an_answer_that_decides_NEITHER_way_is_UNKNOWN_not_refusal() {
        // A missing or malformed `accepted` leaves this process unable to say
        // what the node did with bytes it may well have applied. Reading it as
        // a refusal is what invites the second transfer.
        for verdict in [
            serde_json::json!({}),
            serde_json::json!({"accepted": "yes", "turn_hash": WANT}),
            serde_json::json!({"turn_hash": WANT}),
        ] {
            assert!(
                matches!(bind_admission("transfer", WANT, &verdict), Admission::Unknown(_)),
                "{verdict} must be UNKNOWN, never Refused"
            );
        }
    }

    #[test]
    fn a_refusal_THAT_NAMES_THIS_TURN_is_decided_and_carries_its_reason() {
        // MUST-MISS beside the UNKNOWN poles: this one the node DID decide
        // ABOUT THIS TURN, so it must not be reported as something that might
        // have committed. The node's reject path fills turn_hash before it
        // decides, so a real refusal names the turn it refused.
        assert_eq!(
            bind_admission("transfer", WANT, &serde_json::json!({
                "accepted": false, "turn_hash": WANT,
                "error": "insufficient balance"
            })),
            Admission::Refused("insufficient balance".to_string())
        );
        assert_eq!(
            bind_admission("transfer", WANT, &serde_json::json!({
                "accepted": false, "turn_hash": WANT.to_uppercase()
            })),
            Admission::Refused("no reason given".to_string())
        );
    }

    #[test]
    fn a_refusal_that_names_NO_turn_or_ANOTHER_turn_is_UNKNOWN() {
        // THE NEGATIVE POLE OF THE IDENTITY RULE, and the oracle that used to
        // sit here asserted the opposite: a reply carrying no hash, or someone
        // else's, was reported as a decided refusal, so the caller was told
        // nothing moved on the strength of an answer that never named this
        // turn. Identity is established before the answer is trusted, in BOTH
        // directions.
        for verdict in [
            serde_json::json!({"accepted": false, "error": "insufficient balance"}),
            serde_json::json!({"accepted": false, "turn_hash": OTHER}),
            serde_json::json!({"accepted": false, "turn_hash": 12}),
        ] {
            assert!(
                matches!(bind_admission("transfer", WANT, &verdict), Admission::Unknown(_)),
                "{verdict} names no evidence about this turn, so it is UNKNOWN"
            );
        }
    }

    #[test]
    fn a_healthy_repeat_install_is_not_a_missing_export() {
        // INSTALL IS ONCE PER PROCESS, so every call after the first answers
        // AlreadyInstalled — which the outcome's own docs call healthy. Reading
        // only Installed as healthy meant that on a GOOD archive the first arm
        // ran and every later one skipped with a missing-export reason that was
        // false, so at most one composed control could ever execute.
        use dregg_sdk::{MlDsaKeygenCoreRealInstall as K, MlDsaSignCoreRealInstall as S};
        for sign in [S::Installed, S::AlreadyInstalled] {
            for keygen in [K::Installed, K::AlreadyInstalled] {
                assert!(cores_are_healthy(sign, keygen),
                        "{sign:?}/{keygen:?} is a healthy verified producer");
            }
        }
        // MUST-MISS: only a genuinely absent export is unhealthy, and it must
        // be unhealthy whichever side is missing.
        for (sign, keygen) in [
            (S::ExportAbsent, K::Installed),
            (S::Installed, K::ExportAbsent),
            (S::ExportAbsent, K::ExportAbsent),
            (S::ExportAbsent, K::AlreadyInstalled),
        ] {
            assert!(!cores_are_healthy(sign, keygen),
                    "{sign:?}/{keygen:?} cannot sign a turn");
        }
    }

    #[test]
    fn every_post_submit_unknown_carries_the_reread_and_the_warning() {
        // The guidance is the product here: a nonzero exit that does not say
        // this is the exit a caller resubmits on.
        let e = unknown_after_submit(
            "the answer was lost".to_string(), 100,
            "http://node/api/starbridge/receipts?turn_hash=abc");
        let text = e.to_string();
        assert!(text.contains("UNKNOWN, not a refusal"), "{text}");
        assert!(text.contains("Do NOT resubmit"), "{text}");
        assert!(text.contains("moves 100 again"), "{text}");
        assert!(text.contains("starbridge/receipts?turn_hash=abc"), "{text}");
    }

    // ── the composed transfer path, against a node that answers ─────────────
    //
    // The two roots below live in cmd_transfer's COMPOSITION and no helper
    // test can reach them: one is which hash the confirmation binds to, the
    // other is how an exit after the POST is reported. Both need a submission
    // and a poll, so this mock serves the whole path — /status, the cell, the
    // chain head, the faucet, /turns/submit and the exact-hash receipt query —
    // and DREGG_HOME points the profile loader at a temp identity so no real
    // key is touched and nothing is signed against a live node.
    //
    // The cell's own receipt head and the node-wide tip are DIFFERENT here, and
    // /turns/submit refuses any turn that does not thread the cell's own head,
    // as a node built after 7ea63fe5d does. So every arm that reaches the POST
    // also checks which head the signer threaded; the real admission check is
    // driven in the node crate's `client_threads_the_agent_scoped_receipt_head`.
    // `Submit::OldSoloNode` is the exception: it admits only the node-wide tip,
    // as a solo node built on 737a69fa4 does.

    /// The source cell's own receipt head, served on `GET /api/cell/{id}`.
    const AGENT_HEAD: [u8; 32] = [0xa5; 32];
    /// The node-wide tip, served on `GET /api/receipts`: another agent's receipt.
    const NODE_TIP: [u8; 32] = [0xc3; 32];

    fn submitted(body: &[u8]) -> dregg_sdk::SignedTurn {
        postcard::from_bytes(body).expect("the client must send a postcard SignedTurn")
    }

    #[derive(Clone)]
    enum Submit {
        /// Behave like the node: decode the postcard turn and echo ITS hash.
        Honest,
        /// Accept, and report a DIFFERENT turn's hash.
        ReportsAnotherTurn,
        /// Accept, and report no hash at all.
        ReportsNoHash,
        /// Answer with an HTTP status rather than a verdict.
        HttpError,
        /// Refuse explicitly, NAMING THIS TURN — the one post-submit answer
        /// that is not UNKNOWN.
        Refuses,
        /// Take the turn honestly, then fail the receipt query. The submission
        /// landed and the poll cannot say what became of it.
        HonestThenPollFails,
        /// A solo node built on 737a69fa4: ONE receipt chain for the whole
        /// node, so it commits a turn threading the node-wide tip and refuses
        /// the agent's own head with its "receipt chain mismatch: ..." text.
        OldSoloNode,
        /// Refuse every turn with "receipt chain mismatch", whatever it
        /// threads, as a node whose head moves between every read would.
        MismatchEveryTime,
    }

    struct TransferNode {
        submit: Submit,
        /// The receipts the exact-hash query serves, by turn hash.
        receipted: Mutex<Vec<String>>,
        /// The `previous_receipt_hash` of every submitted turn, in POST order.
        posted: Mutex<Vec<Option<[u8; 32]>>>,
    }

    async fn transfer_connection(
        mut socket: tokio::net::TcpStream,
        node: Arc<TransferNode>,
    ) {
        let mut request = Vec::new();
        let mut chunk = [0u8; 8192];
        let header_end = loop {
            let Ok(n) = socket.read(&mut chunk).await else { return };
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
            let Ok(n) = socket.read(&mut chunk).await else { return };
            if n == 0 {
                return;
            }
            request.extend_from_slice(&chunk[..n]);
        }
        let line = headers.lines().next().unwrap_or_default().to_string();
        let body = request[header_end..header_end + content_length].to_vec();

        let mut code = 200;
        let response = if line.starts_with("GET /status") {
            serde_json::json!({"federation_mode": "solo", "public_key": "11".repeat(32)})
        } else if line.starts_with("GET /api/cell/") {
            serde_json::json!({
                "found": true, "balance": 1_000_000, "nonce": 0,
                "last_receipt_hash": hex::encode(AGENT_HEAD),
            })
        } else if line.starts_with("GET /api/receipts") {
            serde_json::json!([{
                "chain_index": 9, "chain_head": true,
                "receipt_hash": hex::encode(NODE_TIP), "turn_hash": "77".repeat(32),
            }])
        } else if line.starts_with("POST /api/faucet") {
            serde_json::json!({"success": true, "turn_hash": "22".repeat(32)})
        } else if line.starts_with("POST /turns/submit") {
            let turn = submitted(&body).turn;
            let prev = turn.previous_receipt_hash;
            // Every refusal below names the turn it refused, which is what the
            // node's own reject path does.
            let hash = hex::encode(turn.hash());
            node.posted.lock().await.push(prev);
            // The one head this node admits, if any.
            let admits = match node.submit {
                Submit::OldSoloNode => Some(NODE_TIP),
                Submit::MismatchEveryTime => None,
                _ => Some(AGENT_HEAD),
            };
            if admits.is_none() || prev != admits {
                let error = if matches!(node.submit, Submit::OldSoloNode) {
                    // The old node's text: its own prefix around the cipherclerk's.
                    format!(
                        "receipt chain mismatch: receipt chain mismatch: cipherclerk head = \
                         {admits:?}, receipt's prev = {prev:?}"
                    )
                } else {
                    "receipt chain mismatch".to_string()
                };
                serde_json::json!({"accepted": false, "turn_hash": hash, "error": error})
            } else {
                match node.submit.clone() {
                    Submit::HttpError => {
                        code = 503;
                        serde_json::json!({"error": "upstream unavailable"})
                    }
                    Submit::Refuses => serde_json::json!({
                        "accepted": false, "turn_hash": hash, "error": "insufficient balance"
                    }),
                    Submit::ReportsNoHash => serde_json::json!({"accepted": true}),
                    Submit::ReportsAnotherTurn => {
                        let other = "33".repeat(32);
                        node.receipted.lock().await.push(other.clone());
                        serde_json::json!({"accepted": true, "turn_hash": other})
                    }
                    Submit::Honest | Submit::HonestThenPollFails | Submit::OldSoloNode => {
                        node.receipted.lock().await.push(hash.clone());
                        serde_json::json!({"accepted": true, "turn_hash": hash})
                    }
                    Submit::MismatchEveryTime => unreachable!("it admits no head"),
                }
            }
        } else if line.starts_with("GET /api/starbridge/receipts")
            && matches!(node.submit, Submit::HonestThenPollFails)
        {
            code = 500;
            serde_json::json!({"error": "receipt index unavailable"})
        } else if line.starts_with("GET /api/starbridge/receipts") {
            let want = line
                .split("turn_hash=")
                .nth(1)
                .and_then(|rest| rest.split_whitespace().next())
                .unwrap_or_default()
                .to_string();
            let held = node.receipted.lock().await.clone();
            if held.iter().any(|h| h.eq_ignore_ascii_case(&want)) {
                serde_json::json!([{
                    "chain_index": 3, "chain_head": true,
                    "receipt_hash": "44".repeat(32),
                    "turn_hash": want, "finality": "tentative",
                }])
            } else {
                serde_json::json!([])
            }
        } else {
            code = 404;
            serde_json::json!({"error": "not found"})
        };
        let bytes = serde_json::to_vec(&response).unwrap();
        let head = format!(
            "HTTP/1.1 {code} OK\r\ncontent-type: application/json\r\ncontent-length: {}\r\nconnection: close\r\n\r\n",
            bytes.len()
        );
        let _ = socket.write_all(head.as_bytes()).await;
        let _ = socket.write_all(&bytes).await;
    }

    /// A temp DREGG_HOME with one profile, and a node speaking the whole path.
    async fn transfer_fixture(
        submit: Submit,
    ) -> Option<(
        String,
        String,
        tokio::task::JoinHandle<()>,
        Arc<TransferNode>,
    )> {
        // The same install `main` performs, keygen included: creating the
        // temp identity below IS a keygen.
        //
        // MEASURED ON THIS BUILD: all three come back ExportAbsent, so the
        // linked archive exports no verified core and dregg-pq ABORTS the
        // process the moment a key is generated or a turn is signed. These
        // arms therefore cannot run here, and they say so rather than being
        // deleted or quietly passing: the composition they cover is the one a
        // helper cannot reach, so a skipped arm is a known gap and a removed
        // one is an invisible gap. They run unchanged wherever the archive
        // exports the cores. Forcing them through by accepting the unaudited
        // primitive is NOT done: a test is not a reason to turn off an audit
        // gate, and the gate is reporting a real degradation of this build.
        let sign = dregg_sdk::install_verified_mldsa_sign_core_real();
        let keygen = dregg_sdk::install_verified_mldsa_keygen_core_real();
        dregg_sdk::install_verified_mldsa_verify_core();
        if !cores_are_healthy(sign, keygen) {
            return None;
        }
        let node = Arc::new(TransferNode {
            submit,
            receipted: Mutex::new(Vec::new()),
            posted: Mutex::new(Vec::new()),
        });
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let url = format!("http://{}", listener.local_addr().unwrap());
        let shared = node.clone();
        let handle = tokio::spawn(async move {
            while let Ok((socket, _)) = listener.accept().await {
                tokio::spawn(transfer_connection(socket, shared.clone()));
            }
        });
        let home = std::env::temp_dir().join(format!(
            "dregg-client-sign-test-{}",
            listener_port(&url)
        ));
        let _ = std::fs::create_dir_all(home.join("profiles"));
        Some((url, home.to_string_lossy().into_owned(), handle, node))
    }

    fn listener_port(url: &str) -> String {
        url.rsplit(':').next().unwrap_or("0").to_string()
    }

    fn transfer_flags(url: &str, to: &str) -> Flags {
        Flags {
            node_url: url.trim_end_matches('/').to_string(),
            profile: Some("hc2-transfer-test".to_string()),
            token: Some("test-bearer".to_string()),
            topic: "client-sign".to_string(),
            to: Some(to.to_string()),
            fund: 5000,
            amount: Some(100),
            accept_tentative: true,
            rest: Vec::new(),
        }
    }

    /// Which verb a composed run drives.
    #[derive(Clone, Copy)]
    enum Verb {
        Transfer,
        Send,
    }

    /// The whole composed run, with the process-global env seams held for the
    /// duration. `DREGG_HOME` is what keeps this off any real identity.
    /// Returns the verb's result and the head each POST threaded, in order.
    /// `None` when this build cannot run the composed path at all — see
    /// `transfer_fixture`. Every arm below reports the skip rather than
    /// passing on it, so a gap stays visible.
    async fn run_verb(submit: Submit, verb: Verb) -> Option<(Result<()>, Vec<Option<[u8; 32]>>)> {
        // DREGG_HOME AND DREGG_PROFILE ARE PROCESS-GLOBAL, so these arms are
        // serialized: cargo runs tests on threads, and two of them setting the
        // same variables would make each one read the other's identity.
        static ENV: std::sync::Mutex<()> = std::sync::Mutex::new(());
        let _held = ENV.lock().unwrap_or_else(|e| e.into_inner());
        let (url, home, handle, node) = transfer_fixture(submit).await?;
        unsafe {
            std::env::set_var("DREGG_HOME", &home);
            std::env::set_var("DREGG_PROFILE", "hc2-transfer-test");
        }
        let _ = dregg_sdk::profiles::create("hc2-transfer-test");
        let to = "55".repeat(32);
        let out = match verb {
            Verb::Transfer => cmd_transfer(transfer_flags(&url, &to)).await,
            Verb::Send => {
                cmd_send(Flags {
                    to: None,
                    amount: None,
                    rest: vec!["retry probe".to_string()],
                    ..transfer_flags(&url, &to)
                })
                .await
            }
        };
        handle.abort();
        let posted = node.posted.lock().await.clone();
        Some((out, posted))
    }

    async fn run_transfer(submit: Submit) -> Option<Result<()>> {
        run_verb(submit, Verb::Transfer).await.map(|(out, _)| out)
    }

    /// The one place the skip is announced, so a reader of the output sees
    /// WHICH property went unexercised and why.
    fn skipped(what: &str) {
        eprintln!(
            "SKIPPED {what}: this build's linked archive exports no verified \
             ML-DSA core, so signing a turn would abort the process. The arm \
             is unchanged and runs wherever the cores are exported."
        );
    }

    #[test]
    fn probe_which_verified_pq_cores_this_build_exports() {
        eprintln!("PQPROBE sign={:?}", dregg_sdk::install_verified_mldsa_sign_core_real());
        eprintln!("PQPROBE verify={:?}", dregg_sdk::install_verified_mldsa_verify_core());
        eprintln!("PQPROBE keygen={:?}", dregg_sdk::install_verified_mldsa_keygen_core_real());
    }

    #[tokio::test]
    async fn a_transfer_the_node_commits_reports_committed() {
        // UNCONDITIONAL POSITIVE FIRST, through the whole path: without it the
        // refusals below could all be satisfied by a verb that never succeeds.
        let Some(out) = run_transfer(Submit::Honest).await else {
            return skipped("the committed-transfer positive");
        };
        out.expect("an honest node's committed transfer must report success");
    }

    #[tokio::test]
    async fn a_receipt_for_ANOTHER_turn_never_reports_THIS_transfer_committed() {
        // THE WRONG-OPERATION SUCCESS. The node accepts and names a different
        // turn; that other turn has a perfectly valid receipt. Binding the
        // confirmation to the hash the SERVER chose would confirm B and print
        // THIS transfer's recipient and amount beside it.
        let Some(out) = run_transfer(Submit::ReportsAnotherTurn).await else {
            return skipped("the wrong-operation-success pole");
        };
        let e = out.expect_err("a foreign turn hash must never confirm this transfer");
        let text = e.to_string();
        assert!(text.contains("is not the transfer this process signed"), "{text}");
        assert!(text.contains("Do NOT resubmit"), "{text}");
    }

    #[tokio::test]
    async fn every_exit_after_the_post_says_UNKNOWN_and_do_not_resubmit() {
        // A nonzero exit is not proof of refusal. Each of these leaves the
        // bytes possibly delivered, so each must carry the same guidance.
        for submit in [Submit::HttpError, Submit::ReportsNoHash] {
            let Some(out) = run_transfer(submit).await else {
                return skipped("the post-submit UNKNOWN poles");
            };
            let e = out.expect_err("must not succeed");
            let text = e.to_string();
            assert!(text.contains("UNKNOWN, not a refusal"), "{text}");
            assert!(text.contains("Do NOT resubmit"), "{text}");
            assert!(text.contains("starbridge/receipts"),
                    "the caller is owed the exact re-read: {text}");
        }
    }

    #[tokio::test]
    async fn a_poll_that_fails_after_the_turn_landed_is_UNKNOWN() {
        // THE POLE THE REVIEW ASKED FOR: the submission reached the node and
        // the receipt query then failed, so this process cannot say whether
        // the transfer committed. Exiting on it without the warning is what
        // invites the caller to send again.
        let Some(out) = run_transfer(Submit::HonestThenPollFails).await else {
            return skipped("the uncertain-poll pole");
        };
        let e = out.expect_err("a failed poll must not report success");
        let text = e.to_string();
        assert!(text.contains("UNKNOWN, not a refusal"), "{text}");
        assert!(text.contains("Do NOT resubmit"), "{text}");
        assert!(text.contains("starbridge/receipts"), "{text}");
    }

    #[tokio::test]
    async fn an_explicit_refusal_is_the_one_post_submit_answer_that_is_not_unknown() {
        // MUST-MISS beside the arm above: the node executed and rejected, so
        // nothing moved and there is nothing to re-read. Telling the caller
        // this might have committed would be its own false alarm.
        let Some(out) = run_transfer(Submit::Refuses).await else {
            return skipped("the decided-refusal must-miss");
        };
        let e = out.expect_err("a refused transfer must not succeed");
        let text = e.to_string();
        assert!(text.contains("node refused the transfer"), "{text}");
        assert!(!text.contains("UNKNOWN"), "a decided refusal is not UNKNOWN: {text}");
    }

    // ── the one retry on the node-wide head, through both verbs ─────────────

    #[tokio::test]
    async fn an_old_solo_node_commits_the_one_retry_on_the_node_wide_head() {
        // THE OLD DEPLOYED NODE refuses the agent's own head and commits the
        // node-wide tip. Each verb threads its own head first, then retries
        // exactly once on the tip, and confirms the RETRIED turn: the mock
        // receipts only the turn it admitted, so a confirmation bound to the
        // first, refused turn would time out instead of succeeding.
        for verb in [Verb::Transfer, Verb::Send] {
            let Some((out, posted)) = run_verb(Submit::OldSoloNode, verb).await else {
                return skipped("the old-solo-node retry");
            };
            out.expect("the retry on the node-wide head must commit");
            assert_eq!(posted, vec![Some(AGENT_HEAD), Some(NODE_TIP)]);
        }
    }

    #[tokio::test]
    async fn the_own_head_that_commits_and_any_other_refusal_are_never_retried() {
        // MUST-MISS beside the arm above. A node that keeps a head per agent
        // commits the first attempt, and a refusal for any other reason is
        // final: either way there is exactly one POST, on the agent's own head.
        for verb in [Verb::Transfer, Verb::Send] {
            let Some((out, posted)) = run_verb(Submit::Honest, verb).await else {
                return skipped("the no-retry must-miss");
            };
            out.expect("a node that admits the own head commits the first attempt");
            assert_eq!(posted, vec![Some(AGENT_HEAD)]);

            let Some((out, posted)) = run_verb(Submit::Refuses, verb).await else {
                return skipped("the no-retry must-miss");
            };
            let text = out
                .expect_err("a refused turn must not succeed")
                .to_string();
            assert!(text.contains("insufficient balance"), "{text}");
            assert_eq!(
                posted,
                vec![Some(AGENT_HEAD)],
                "another refusal is never retried"
            );
        }
    }

    #[tokio::test]
    async fn a_second_chain_mismatch_is_surfaced_and_not_retried_again() {
        // EXACTLY ONCE. The retry's own mismatch goes back to the caller as the
        // decided refusal it is: nothing moved, so it is not UNKNOWN.
        for verb in [Verb::Transfer, Verb::Send] {
            let Some((out, posted)) = run_verb(Submit::MismatchEveryTime, verb).await else {
                return skipped("the one-retry bound");
            };
            let text = out
                .expect_err("a refused retry must not succeed")
                .to_string();
            assert!(text.contains("node refused the"), "{text}");
            assert!(text.contains("receipt chain mismatch"), "{text}");
            assert!(
                !text.contains("UNKNOWN"),
                "a decided refusal is not UNKNOWN: {text}"
            );
            assert_eq!(
                posted,
                vec![Some(AGENT_HEAD), Some(NODE_TIP)],
                "exactly one retry"
            );
        }
    }
}
