//! Client for the dregg devnet API.

use crate::cipherclerk::UserCipherclerk;
use dregg_sdk::{CellId, SignedTurn};
use dregg_turn::{Action, Effect};
use reqwest::header::{AUTHORIZATION, HeaderMap, HeaderValue};
use serde::Deserialize;
use std::env;

/// Client for communicating with the dregg devnet.
#[derive(Clone)]
pub struct DevnetClient {
    base_url: String,
    client: reqwest::Client,
}

// ─── Explorer response types ────────────────────────────────────────────────

/// An event from the devnet activity stream.
#[derive(Clone, Debug, Deserialize)]
pub struct RecentEvent {
    pub event_type: String,
    pub summary: String,
    pub timestamp: String,
    pub cell_id: Option<String>,
    pub tx_hash: Option<String>,
}

/// Response from the events endpoint.
#[derive(Clone, Debug, Deserialize)]
pub struct EventsResponse {
    pub block_height: u64,
    pub events: Vec<RecentEvent>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct CellDetails {
    #[serde(alias = "id")]
    pub cell_id: String,
    #[serde(default = "default_hosted_mode")]
    pub mode: String,
    pub balance: u64,
    pub nonce: u64,
    #[serde(alias = "capability_count")]
    pub capabilities_count: u32,
    #[serde(default)]
    pub program_vk: Option<String>,
    #[serde(default)]
    pub provenance: Option<String>,
    #[serde(default)]
    pub created_by_factory: Option<String>,
    /// Per-slot field values (64-hex strings), when the node exposes them
    /// (`/api/cell/{id}` does). `default` keeps older node responses valid.
    #[serde(default)]
    pub fields: Vec<String>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct TurnEffect {
    pub effect_type: String,
    pub details: String,
}

#[derive(Debug, Clone, Deserialize)]
pub struct TurnDetails {
    pub turn_hash: String,
    pub signer: String,
    pub effects: Vec<TurnEffect>,
    pub fee: u64,
    pub result: String,
    pub proof_type: String,
}

#[derive(Debug, Clone, Deserialize)]
pub struct BlockDetails {
    pub height: u64,
    pub transactions: Vec<String>,
    pub root_hash: String,
    pub timestamp: String,
    pub proposer: String,
}

#[derive(Debug, Clone, Deserialize)]
pub struct NoteStatus {
    pub commitment: String,
    pub status: String,
    pub nullifier_exists: bool,
}

#[derive(Debug, Clone, Deserialize)]
pub struct ProofDetails {
    pub hash: String,
    pub air_name: String,
    pub trace_size: u64,
    pub public_inputs_count: u32,
    pub verified: bool,
}

#[derive(Debug, Clone, Deserialize)]
pub struct FactoryDetails {
    pub vk_hash: String,
    pub descriptor: String,
    pub creation_budget: u64,
    pub cells_created: u32,
    pub vk_strategy: String,
}

#[derive(Debug, Clone, Deserialize)]
pub struct SearchResult {
    pub kind: String,
    pub id: String,
    pub summary: String,
}

#[derive(Debug, Clone, Deserialize)]
pub struct ExplorerStats {
    pub block_height: u64,
    pub total_cells_hosted: u64,
    pub total_cells_sovereign: u64,
    pub total_notes_spent: u64,
    pub total_notes_unspent: u64,
    pub turns_this_epoch: u64,
    pub active_auctions: u64,
    pub federation_nodes_up: u32,
    pub federation_nodes_total: u32,
}

#[derive(Debug, Clone, Deserialize)]
struct ReceiptInfo {
    pub chain_index: u64,
    pub chain_head: bool,
    pub receipt_hash: String,
    pub turn_hash: String,
    pub agent: String,
    pub computrons_used: u64,
    pub action_count: usize,
    pub finality: String,
    pub has_proof: bool,
    /// Node policy hint: not_required means signature attestation only.
    #[serde(default)]
    pub proof_status: Option<String>,
    pub executor_signed: bool,
    #[serde(default)]
    pub has_witness: bool,
    #[serde(default)]
    pub witness_count: usize,
}

#[derive(Debug, Clone, Deserialize)]
struct AttestedRootInfo {
    pub height: u64,
    pub merkle_root: String,
    pub timestamp: i64,
    pub signatures: usize,
}

#[derive(Debug, Clone, Deserialize)]
struct CellListEntry {
    pub id: String,
    pub balance: u64,
    pub nonce: u64,
    pub capability_count: u32,
    #[serde(default)]
    pub has_program: bool,
}

#[derive(Debug, Clone, Deserialize)]
struct CommittedEventWire {
    height: u64,
    turn_hash: String,
    cell_id: String,
    #[serde(default)]
    effects: Vec<String>,
    timestamp: i64,
}

#[derive(Debug, Clone, Deserialize)]
struct FaucetResponse {
    success: bool,
    amount: u64,
    error: Option<String>,
}

fn default_hosted_mode() -> String {
    "hosted".to_string()
}

fn events_response_from_committed(
    committed: Vec<CommittedEventWire>,
    fallback_height: u64,
) -> EventsResponse {
    let block_height = committed
        .iter()
        .map(|event| event.height)
        .max()
        .unwrap_or(fallback_height);
    EventsResponse {
        block_height,
        events: committed_events_to_recent(committed),
    }
}

fn committed_events_to_recent(committed: Vec<CommittedEventWire>) -> Vec<RecentEvent> {
    committed
        .into_iter()
        .map(|event| RecentEvent {
            event_type: "turn".to_string(),
            summary: if event.effects.is_empty() {
                format!("Committed turn {}", short_hash(&event.turn_hash))
            } else {
                event.effects.join(", ")
            },
            timestamp: event.timestamp.to_string(),
            cell_id: Some(event.cell_id),
            tx_hash: Some(event.turn_hash),
        })
        .collect()
}

fn short_hash(hash: &str) -> String {
    format!("{}...", &hash[..12.min(hash.len())])
}

fn parse_cell_id(hex_cell: &str) -> Result<CellId, DevnetError> {
    let bytes = hex::decode(hex_cell.trim()).map_err(|e| {
        DevnetError::Api(format!("invalid cell id `{hex_cell}`: expected hex: {e}"))
    })?;
    let bytes: [u8; 32] = bytes.try_into().map_err(|bytes: Vec<u8>| {
        DevnetError::Api(format!(
            "invalid cell id `{hex_cell}`: expected 32 bytes, got {}",
            bytes.len()
        ))
    })?;
    Ok(CellId(bytes))
}

#[derive(Debug, Clone, Deserialize)]
pub struct SubmitSignedTurnResult {
    pub accepted: bool,
    pub turn_hash: Option<String>,
    pub signer: Option<String>,
    pub action_count: usize,
    pub error: Option<String>,
}

// ─── Gallery response types ────────────────────────────────────────────────

#[derive(Debug, Clone, Deserialize)]
pub struct Artwork {
    pub id: String,
    pub title: String,
    pub artist: String,
    pub description: String,
}

#[derive(Debug, Clone, Deserialize)]
pub struct Auction {
    pub id: String,
    pub artwork_id: String,
    pub title: String,
    pub current_bid: u64,
    pub bidder: Option<String>,
    pub ends_at: String,
}

#[derive(Debug, Clone, Deserialize)]
pub struct BidInfo {
    pub auction_id: String,
    pub title: String,
    pub amount: u64,
    pub status: String,
}

// ─── Identity response types ──────────────────────────────────────────────

#[derive(Debug, Clone, Deserialize)]
pub struct ProofRequestResult {
    pub request_id: String,
    pub status: String,
}

#[derive(Debug, Clone, Deserialize)]
pub struct CredentialInfo {
    pub credential_id: String,
    pub schema: String,
    pub issuer: String,
    pub issued_at: String,
}

#[derive(Debug, Clone, Deserialize)]
pub struct IdentityCredentialCheckpoint {
    pub source: String,
    pub chain_index: u64,
    pub receipt_hash: String,
    pub turn_hash: String,
    pub issuer_cell: String,
    #[serde(default)]
    pub subject_cells: Vec<String>,
    pub timestamp: i64,
    pub effects_hash: String,
    pub event_count: usize,
    pub derivation_record_count: usize,
    pub proof_status: String,
    pub finality: String,
}

#[derive(Debug, Clone, Deserialize)]
pub struct IdentityProofCheckpoint {
    pub source: String,
    pub chain_index: u64,
    pub receipt_hash: String,
    pub turn_hash: String,
    pub cell_id: String,
    pub timestamp: i64,
    pub effects_hash: String,
    pub proof_status: String,
    pub executor_signed: bool,
    pub witness_count: usize,
    pub finality: String,
}

// ─── Status response types ────────────────────────────────────────────────

#[derive(Debug, Clone, Deserialize)]
pub struct FederationHealth {
    pub status: String,
    pub nodes_up: u32,
    pub nodes_total: u32,
    pub block_height: u64,
    pub last_block_time: String,
    pub avg_block_time_ms: u64,
}

#[derive(Debug, Clone, Deserialize)]
struct NodeStatusResponse {
    healthy: bool,
    peer_count: u32,
    latest_height: u64,
    #[serde(default)]
    note_count: u64,
    federation_mode: String,
    #[serde(default)]
    dag_height: u64,
    #[serde(default)]
    consensus_live: bool,
    #[serde(default)]
    public_key: String,
    /// Hex of the id the node's executor signs and verifies under
    /// (`executor_setup::federation_id_for_executor`). Empty when an older node
    /// does not serve it; the preflight treats that as a refusal, not a cue to
    /// derive a value.
    #[serde(default)]
    executor_federation_id: String,
}

/// A compact, operator-facing summary of a node's identity + liveness, used by
/// the startup preflight to catch the two most common misconfigurations early:
/// an unreachable `DEVNET_URL` and a `FEDERATION_ID` that won't match the
/// node's executor signing domain (which silently breaks every transfer).
#[derive(Debug, Clone)]
pub struct NodePreflight {
    pub reachable: bool,
    pub healthy: bool,
    pub consensus_live: bool,
    pub federation_mode: String,
    pub dag_height: u64,
    pub latest_height: u64,
    /// The id the node's executor signs and verifies under, as the node serves
    /// it on `/status`. The bot's `FEDERATION_ID` must equal it for transfers to
    /// verify. It is NOT derivable from `federation_mode`: a configured committee
    /// of one reports "solo" and signs under its genesis federation id, not
    /// `blake3(public_key)` (breadstuffs #90 / 33f150b16).
    pub executor_federation_id: String,
    /// If unreachable, why (timeout / connect refused / HTTP error).
    pub error: Option<String>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct ProofVerifyResult {
    pub valid: bool,
    pub air_name: Option<String>,
    pub public_inputs: Option<Vec<String>>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct DevnetMetrics {
    pub tps: f64,
    pub block_height: u64,
    pub pending_turns: u64,
    pub active_cells: u64,
    pub memory_usage_mb: u64,
    pub uptime_secs: u64,
}

// ─── Error type ─────────────────────────────────────────────────────────────

#[derive(Debug)]
pub enum DevnetError {
    Http(reqwest::Error),
    /// A non-success HTTP response, carrying the status code and the node's
    /// response body. Prefer this over `Api` for live-node calls so
    /// [`DevnetError::user_message`] can classify the failure (auth gate, rate
    /// limit, node down, …) into actionable guidance for the user.
    Status {
        code: u16,
        body: String,
    },
    /// An opaque, already-formatted error string (decode failures, app-level
    /// rejections from a JSON `success:false` body, etc).
    Api(String),
    Unsupported(&'static str),
}

impl DevnetError {
    /// Build a `Status` error from a non-success response, draining its body.
    /// Truncates the body so a giant HTML error page can't blow up a Discord
    /// embed.
    pub async fn from_response(resp: reqwest::Response) -> Self {
        let code = resp.status().as_u16();
        let mut body = resp.text().await.unwrap_or_default();
        // Collapse whitespace + cap length; node JSON/text errors are short,
        // but a misrouted request can return a full HTML page.
        body = body.trim().chars().take(400).collect();
        DevnetError::Status { code, body }
    }

    /// Render an actionable, user-facing message for a Discord embed. `action`
    /// is a short verb phrase describing what the user was doing
    /// (e.g. "submit the transfer", "request faucet tokens") so the guidance
    /// reads naturally. This never leaks a raw HTML body or a bare status line.
    ///
    /// ⚑ **It also emits the operator half** ([`operator_diagnostic`](Self::operator_diagnostic))
    /// whenever there is one, so the detail this sentence deliberately withholds cannot be lost by a
    /// call site forgetting to log it — there are ~30 call sites and asking each to remember is how a
    /// gate becomes optional. `#[track_caller]` names the refusing site in the log line.
    #[track_caller]
    pub fn user_message(&self, action: &str) -> String {
        if let Some(detail) = self.operator_diagnostic() {
            let at = std::panic::Location::caller();
            tracing::error!(
                target: "dregg::refusal",
                at = %at,
                action,
                detail = %detail,
                "a node request failed for a reason only an operator can fix; the player was told \
                 nothing was changed and that it is our side"
            );
        }
        self.player_message(action)
    }

    /// The player's sentence alone (no logging) — the body of [`user_message`](Self::user_message),
    /// split out so the copy is testable without a subscriber and so the logging cannot recurse.
    fn player_message(&self, action: &str) -> String {
        match self {
            DevnetError::Http(e) => {
                if e.is_timeout() {
                    format!(
                        "The node didn't respond in time while trying to {action}. The devnet may be busy; try again in a moment."
                    )
                } else if e.is_connect() {
                    format!(
                        "Couldn't reach the node to {action}. The devnet may be offline; check `/status`."
                    )
                } else {
                    format!("Network error while trying to {action}: {e}")
                }
            }
            DevnetError::Status { code, body } => {
                let hint = body_hint(body);
                match *code {
                    400 | 422 => format!(
                        "The node rejected the request to {action} (HTTP {code}).{hint} Nothing was changed. This usually means a malformed turn, or a value the rules would not accept."
                    ),
                    // ⚑ NEVER NAME THE ENV VAR. This was the purest "name a symbol as the fix"
                    // instance in the tree: it told a PLAYER to set `DEVNET_API_TOKEN` "for the bot",
                    // which they cannot do, on a machine they do not have, for a process they do not
                    // run. The env var is the OPERATOR's fix and lives in
                    // [`DevnetError::operator_diagnostic`]; the player gets the two things that are
                    // true for them — nothing landed, and this is our side.
                    401 | 403 => format!(
                        "This node will not accept a write to {action} from us, so nothing was changed. That is a permission problem on our side, not with what you asked for; the server log names what an operator has to set."
                    ),
                    404 => format!(
                        "The node has no record for this {action} request (HTTP 404).{hint} The cell/turn/name may not exist yet; try `/faucet` to materialize your cell first."
                    ),
                    409 => format!(
                        "Conflict while trying to {action} (HTTP 409).{hint} Someone may have taken this name, or your nonce is stale; try again."
                    ),
                    429 => format!(
                        "Rate limited while trying to {action} (HTTP 429). The node caps turns per minute; wait a bit and retry."
                    ),
                    500..=599 => format!(
                        "The node hit an internal error trying to {action} (HTTP {code}).{hint} This is a node-side fault, not your input; try again or check `/status`."
                    ),
                    _ => format!("The node returned HTTP {code} while trying to {action}.{hint}"),
                }
            }
            DevnetError::Api(msg) => {
                // App-level rejection (e.g. faucet success:false, insufficient
                // balance surfaced by the executor). Surface it but framed.
                let m = msg.trim();
                if m.is_empty() {
                    format!("The node rejected the request to {action} without a reason.")
                } else if m.to_lowercase().contains("insufficient")
                    || m.to_lowercase().contains("balance")
                {
                    format!("Couldn't {action}: {m}. Top up with `/faucet`.")
                } else {
                    format!("Couldn't {action}: {m}")
                }
            }
            DevnetError::Unsupported(msg) => {
                format!("That isn't available on this node yet ({msg}).")
            }
        }
    }

    /// ⚑ **THE OPERATOR HALF** — `Some(detail)` exactly for the class of failure where the fix is
    /// something only an operator can do, `None` when [`user_message`](Self::user_message) already
    /// tells the whole story.
    ///
    /// This exists because the 401/403 sentence used to BE the operator's note: it told a player to
    /// "set `DEVNET_API_TOKEN` for the bot", naming an environment variable on a machine they have no
    /// access to. Removing that from the player copy without filing it somewhere would have traded one
    /// bad failure mode for another, so it is filed here — the same audience split as
    /// `cell::program::ProgramError::operator_diagnostic`. Callers emit it at `tracing::error!` beside
    /// the message they show.
    pub fn operator_diagnostic(&self) -> Option<String> {
        match self {
            DevnetError::Status {
                code: code @ (401 | 403),
                body,
            } => Some(format!(
                "the node refused a WRITE as unauthorized (HTTP {code}): it gates writes behind an \
                 operator token. Set `DEVNET_API_TOKEN` for this bot process, or point \
                 `DREGG_NODE_URL` at a node that accepts public turns. Node body: {body}"
            )),
            _ => None,
        }
    }
}

/// Extract a short, human-useful fragment from a node error body for inlining
/// into a user message — skips empty/HTML bodies.
fn body_hint(body: &str) -> String {
    let b = body.trim();
    if b.is_empty() || b.starts_with('<') {
        String::new()
    } else {
        format!(
            " Node said: \"{}\".",
            b.chars().take(160).collect::<String>()
        )
    }
}

impl From<reqwest::Error> for DevnetError {
    fn from(e: reqwest::Error) -> Self {
        DevnetError::Http(e)
    }
}

impl std::fmt::Display for DevnetError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DevnetError::Http(e) => write!(f, "HTTP error: {e}"),
            DevnetError::Status { code, body } => {
                if body.is_empty() {
                    write!(f, "HTTP {code}")
                } else {
                    write!(f, "HTTP {code}: {body}")
                }
            }
            DevnetError::Api(msg) => write!(f, "API error: {msg}"),
            DevnetError::Unsupported(msg) => write!(f, "Unsupported by current devnet API: {msg}"),
        }
    }
}

// ─── Client implementation ──────────────────────────────────────────────────

impl DevnetClient {
    /// Create a new devnet client.
    pub fn new(base_url: &str) -> Self {
        let mut headers = HeaderMap::new();
        if let Ok(token) = env::var("DEVNET_API_TOKEN") {
            if !token.trim().is_empty() {
                let value = format!("Bearer {}", token.trim());
                if let Ok(value) = HeaderValue::from_str(&value) {
                    headers.insert(AUTHORIZATION, value);
                }
            }
        }

        Self {
            base_url: base_url.trim_end_matches('/').to_string(),
            client: reqwest::Client::builder()
                .default_headers(headers)
                .timeout(std::time::Duration::from_secs(10))
                .build()
                .expect("failed to build HTTP client"),
        }
    }

    /// Get a reference to the underlying HTTP client (for custom endpoint calls).
    pub fn client(&self) -> &reqwest::Client {
        &self.client
    }

    /// Submit a caller-signed canonical dregg turn to the node.
    pub async fn submit_signed_turn(
        &self,
        signed: &SignedTurn,
    ) -> Result<SubmitSignedTurnResult, DevnetError> {
        let url = format!("{}/api/turns/submit-signed", self.base_url);
        let body = postcard::to_stdvec(signed)
            .map_err(|e| DevnetError::Api(format!("failed to encode signed turn: {e}")))?;
        let resp = self
            .client
            .post(&url)
            .header("content-type", "application/octet-stream")
            .body(body)
            .send()
            .await?;
        if !resp.status().is_success() {
            return Err(DevnetError::from_response(resp).await);
        }
        Ok(resp.json().await?)
    }

    /// Build, sign, and submit a Starbridge app action from a hosted bot cclerk.
    pub async fn submit_app_action(
        &self,
        cclerk: &UserCipherclerk,
        action: Action,
        memo: Option<String>,
    ) -> Result<SubmitSignedTurnResult, DevnetError> {
        self.submit_app_actions(cclerk, vec![action], memo).await
    }

    /// Build, sign, and submit an atomic set of Starbridge app actions.
    pub async fn submit_app_actions(
        &self,
        cclerk: &UserCipherclerk,
        actions: Vec<Action>,
        memo: Option<String>,
    ) -> Result<SubmitSignedTurnResult, DevnetError> {
        if actions.is_empty() {
            return Err(DevnetError::Api(
                "cannot submit an empty action set".to_string(),
            ));
        }

        let mut turn = if actions.len() == 1 {
            cclerk
                .app
                .make_turn(actions.into_iter().next().expect("checked non-empty"))
        } else {
            cclerk.app.make_turn_with_actions(actions)
        };
        turn.memo = memo;
        turn.nonce = self
            .fetch_cell_nonce(cclerk.cell_id_hex())
            .await
            .unwrap_or(0);

        let signed = cclerk.app.sign_turn(&turn);
        self.submit_signed_turn(&signed).await
    }

    /// Submit a transfer as a canonical Ed25519-signed dregg turn.
    ///
    /// This is the live bot command path for `/send` and `/tip`. The older
    /// JSON `/api/turns/submit` helper below remains only as an explicitly
    /// legacy compatibility surface for deployments that have not yet moved
    /// to `SignedTurn` ingress.
    pub async fn submit_transfer_turn(
        &self,
        cclerk: &UserCipherclerk,
        from_cell: &str,
        to_cell: &str,
        amount: u64,
    ) -> Result<String, DevnetError> {
        let from = parse_cell_id(from_cell)?;
        let to = parse_cell_id(to_cell)?;
        if from.0 != cclerk.cell_id_bytes() {
            return Err(DevnetError::Api(format!(
                "sender identity mismatch: command is linked to {from_cell}, but hosted cclerk is {}",
                cclerk.cell_id_hex()
            )));
        }

        let action = cclerk.app.make_action(
            from,
            "transfer",
            vec![Effect::Transfer { from, to, amount }],
        );
        let result = self
            .submit_app_action(
                cclerk,
                action,
                Some(format!("discord transfer {amount} DEC")),
            )
            .await?;
        if !result.accepted {
            return Err(DevnetError::Api(
                result
                    .error
                    .unwrap_or_else(|| "canonical transfer rejected".to_string()),
            ));
        }
        result
            .turn_hash
            .ok_or_else(|| DevnetError::Api("canonical transfer response omitted turn_hash".into()))
    }

    async fn fetch_cell_nonce(&self, cell_id: &str) -> Result<u64, DevnetError> {
        let url = format!("{}/api/cell/{cell_id}", self.base_url);
        let resp = self.client.get(&url).send().await?;
        if !resp.status().is_success() {
            return Err(DevnetError::from_response(resp).await);
        }
        let value: serde_json::Value = resp.json().await?;
        Ok(value.get("nonce").and_then(|v| v.as_u64()).unwrap_or(0))
    }

    /// Get events since a given block height (for the activity feed poller).
    pub async fn get_events_since(&self, since_height: u64) -> Result<EventsResponse, DevnetError> {
        let url = format!("{}/api/events", self.base_url);
        let resp = self
            .client
            .get(&url)
            .query(&[("since_height", since_height.to_string())])
            .send()
            .await?;
        if !resp.status().is_success() {
            return Err(DevnetError::from_response(resp).await);
        }
        let events: Vec<CommittedEventWire> = resp.json().await?;
        Ok(events_response_from_committed(events, since_height))
    }

    /// Get cell details by ID.
    pub async fn get_cell_details(&self, cell_id: &str) -> Result<CellDetails, DevnetError> {
        let url = format!("{}/api/cell/{cell_id}", self.base_url);
        let resp = self.client.get(&url).send().await?;
        if !resp.status().is_success() {
            return Err(DevnetError::from_response(resp).await);
        }
        Ok(resp.json().await?)
    }

    /// Get turn details by hash.
    pub async fn get_turn_details(&self, turn_hash: &str) -> Result<TurnDetails, DevnetError> {
        let url = format!("{}/api/receipts", self.base_url);
        let resp = self.client.get(&url).send().await?;
        if !resp.status().is_success() {
            return Err(DevnetError::from_response(resp).await);
        }
        let receipts: Vec<ReceiptInfo> = resp.json().await?;
        let receipt = receipts
            .into_iter()
            .find(|receipt| receipt.turn_hash.eq_ignore_ascii_case(turn_hash))
            .ok_or_else(|| DevnetError::Api(format!("turn not found: {turn_hash}")))?;

        Ok(TurnDetails {
            turn_hash: receipt.turn_hash,
            signer: receipt.agent,
            effects: vec![TurnEffect {
                effect_type: "actions".to_string(),
                details: format!("{} action(s) committed", receipt.action_count),
            }],
            fee: receipt.computrons_used,
            result: receipt.finality,
            proof_type: if receipt.proof_status.as_deref() == Some("not_required") {
                "coordination: signature attestation only, no validity proof".to_string()
            } else if receipt.executor_signed || receipt.has_proof {
                if receipt.has_witness {
                    format!(
                        "executor-signed receipt, {} witness artifact(s)",
                        receipt.witness_count
                    )
                } else {
                    "executor-signed receipt".to_string()
                }
            } else if receipt.has_witness {
                format!("receipt, {} witness artifact(s)", receipt.witness_count)
            } else {
                "receipt".to_string()
            },
        })
    }

    /// Get block details by height.
    pub async fn get_block_details(&self, height: u64) -> Result<BlockDetails, DevnetError> {
        let url = format!("{}/api/blocks", self.base_url);
        let resp = self.client.get(&url).send().await?;
        if !resp.status().is_success() {
            return Err(DevnetError::from_response(resp).await);
        }
        let blocks: Vec<AttestedRootInfo> = resp.json().await?;
        let block = blocks
            .into_iter()
            .find(|block| block.height == height)
            .ok_or_else(|| DevnetError::Api(format!("block not found: {height}")))?;
        Ok(BlockDetails {
            height: block.height,
            transactions: Vec::new(),
            root_hash: block.merkle_root,
            timestamp: block.timestamp.to_string(),
            proposer: format!("{} signature(s)", block.signatures),
        })
    }

    /// Get note status by commitment.
    pub async fn get_note_status(&self, _commitment: &str) -> Result<NoteStatus, DevnetError> {
        Err(DevnetError::Unsupported(
            "note-by-commitment lookup is not exposed; /status only reports aggregate note counts",
        ))
    }

    /// Get proof details by hash.
    pub async fn get_proof_details(&self, _hash: &str) -> Result<ProofDetails, DevnetError> {
        Err(DevnetError::Unsupported(
            "proof metadata lookup is not exposed by the current public node API",
        ))
    }

    /// Get factory details by VK hash.
    pub async fn get_factory_details(&self, _vk_hash: &str) -> Result<FactoryDetails, DevnetError> {
        Err(DevnetError::Unsupported(
            "factory lookup is not exposed by the current public node API",
        ))
    }

    /// Search for entities by prefix.
    pub async fn explorer_search(&self, query: &str) -> Result<Vec<SearchResult>, DevnetError> {
        let needle = query.trim().to_ascii_lowercase();
        if needle.is_empty() {
            return Ok(Vec::new());
        }

        let mut results = Vec::new();

        for cell in self.fetch_cells().await.unwrap_or_default() {
            if cell.id.to_ascii_lowercase().contains(&needle) {
                results.push(SearchResult {
                    kind: "cell".to_string(),
                    id: cell.id.clone(),
                    summary: format!(
                        "balance {} DEC, nonce {}, {} capability(s)",
                        cell.balance, cell.nonce, cell.capability_count
                    ),
                });
            }
        }

        for receipt in self.fetch_receipts().await.unwrap_or_default() {
            if receipt.turn_hash.to_ascii_lowercase().contains(&needle)
                || receipt.receipt_hash.to_ascii_lowercase().contains(&needle)
                || receipt.agent.to_ascii_lowercase().contains(&needle)
            {
                results.push(SearchResult {
                    kind: "turn".to_string(),
                    id: receipt.turn_hash.clone(),
                    summary: format!(
                        "{} action(s), {}, chain index {}{}{}",
                        receipt.action_count,
                        receipt.finality,
                        receipt.chain_index,
                        if receipt.has_witness {
                            format!(", {} witness(es)", receipt.witness_count)
                        } else {
                            String::new()
                        },
                        if receipt.chain_head { " (head)" } else { "" }
                    ),
                });
            }
        }

        for block in self.fetch_blocks().await.unwrap_or_default() {
            let height = block.height.to_string();
            if height.contains(&needle) || block.merkle_root.to_ascii_lowercase().contains(&needle)
            {
                results.push(SearchResult {
                    kind: "block".to_string(),
                    id: height,
                    summary: format!(
                        "root {}, {} signature(s)",
                        short_hash(&block.merkle_root),
                        block.signatures
                    ),
                });
            }
        }

        Ok(results)
    }

    /// Get explorer stats.
    pub async fn explorer_stats(&self) -> Result<ExplorerStats, DevnetError> {
        let status = self.node_status().await?;
        let cells = self.fetch_cells().await.unwrap_or_default();
        let receipts = self.fetch_receipts().await.unwrap_or_default();
        let is_solo = status.federation_mode == "solo";
        let nodes_total = if is_solo {
            1
        } else {
            status.peer_count.saturating_add(1)
        };
        let nodes_up = if status.healthy { nodes_total } else { 0 };
        Ok(ExplorerStats {
            block_height: status.latest_height,
            total_cells_hosted: cells.iter().filter(|cell| !cell.has_program).count() as u64,
            total_cells_sovereign: cells.iter().filter(|cell| cell.has_program).count() as u64,
            total_notes_spent: 0,
            total_notes_unspent: status.note_count,
            turns_this_epoch: receipts.len() as u64,
            active_auctions: 0,
            federation_nodes_up: nodes_up,
            federation_nodes_total: nodes_total,
        })
    }

    /// Get recent events, optionally filtered by cell_id.
    pub async fn get_recent_events(
        &self,
        count: u32,
        cell_id: Option<&str>,
    ) -> Result<Vec<RecentEvent>, DevnetError> {
        let url = format!("{}/api/events", self.base_url);
        let count = count.clamp(1, 200) as usize;
        let resp = self
            .client
            .get(&url)
            .query(&[
                ("since_height", "0".to_string()),
                ("limit", "200".to_string()),
            ])
            .send()
            .await?;
        if !resp.status().is_success() {
            return Err(DevnetError::from_response(resp).await);
        }
        let committed: Vec<CommittedEventWire> = resp.json().await?;
        let mut events = committed_events_to_recent(committed);
        if let Some(cid) = cell_id {
            events.retain(|event| event.cell_id.as_deref() == Some(cid));
        }
        if events.len() > count {
            events = events.split_off(events.len() - count);
        }
        events.reverse();
        Ok(events)
    }

    /// Get recent committed turns for a cell that may include identity issuance.
    ///
    /// The current public node event surface does not expose Starbridge action
    /// metadata or the turn memo, so callers must present these as audit
    /// checkpoints rather than as a credential inventory.
    pub async fn get_recent_identity_issue_turns(
        &self,
        cell_id: &str,
        count: u32,
    ) -> Result<Vec<RecentEvent>, DevnetError> {
        self.get_recent_events(count, Some(cell_id)).await
    }

    /// Get real Starbridge identity credential checkpoints from node receipts.
    pub async fn get_identity_credentials(
        &self,
        cell_id: &str,
        count: u32,
    ) -> Result<Vec<IdentityCredentialCheckpoint>, DevnetError> {
        let url = format!("{}/api/starbridge/identity/credentials", self.base_url);
        let resp = self
            .client
            .get(&url)
            .query(&[
                ("cell", cell_id.to_string()),
                ("limit", count.clamp(1, 200).to_string()),
            ])
            .send()
            .await?;
        if !resp.status().is_success() {
            return Err(DevnetError::from_response(resp).await);
        }
        Ok(resp.json().await?)
    }

    /// Get identity proof/audit checkpoints from committed node receipts.
    pub async fn get_identity_proof_checkpoints(
        &self,
        cell_id: &str,
        count: u32,
    ) -> Result<Vec<IdentityProofCheckpoint>, DevnetError> {
        let url = format!(
            "{}/api/starbridge/identity/proof-checkpoints",
            self.base_url
        );
        let resp = self
            .client
            .get(&url)
            .query(&[
                ("cell", cell_id.to_string()),
                ("limit", count.clamp(1, 200).to_string()),
            ])
            .send()
            .await?;
        if !resp.status().is_success() {
            return Err(DevnetError::from_response(resp).await);
        }
        Ok(resp.json().await?)
    }

    /// The explorer base URL for building links — `DREGG_EXPLORER_BASE`, or `None`
    /// when unset. Callers must render a plain copyable id in the `None` case,
    /// never a dead link (the old hardcoded `devnet.dregg.fg-goose.online` no
    /// longer routes anywhere); prefer [`crate::explorer_link`]'s helpers.
    pub fn explorer_base_url(&self) -> Option<String> {
        crate::explorer_link::explorer_base()
    }

    // ─── Cipherclerk / transfer endpoints ───────────────────────────────────────────

    /// Register a cell on devnet.
    pub async fn register_cell(&self, cell_id: &str, public_key: &str) -> Result<(), DevnetError> {
        let url = format!("{}/api/faucet", self.base_url);
        let body = serde_json::json!({
            "recipient": cell_id,
            "public_key": public_key,
            "amount": 0,
        });
        let resp = self.client.post(&url).json(&body).send().await?;
        if !resp.status().is_success() {
            return Err(DevnetError::from_response(resp).await);
        }
        let result: FaucetResponse = resp.json().await?;
        if !result.success {
            return Err(DevnetError::Api(
                result
                    .error
                    .unwrap_or_else(|| "cell materialization failed".to_string()),
            ));
        }
        Ok(())
    }

    /// Get the balance of a cell.
    pub async fn get_balance(&self, cell_id: &str) -> Result<u64, DevnetError> {
        let url = format!("{}/api/cell/{cell_id}", self.base_url);
        let resp = self.client.get(&url).send().await?;
        if !resp.status().is_success() {
            return Err(DevnetError::from_response(resp).await);
        }
        let cell: CellDetails = resp.json().await?;
        Ok(cell.balance)
    }

    /// Submit a transfer through the legacy BLAKE3-MAC JSON endpoint.
    ///
    /// New bot commands should use [`Self::submit_transfer_turn`]. This is
    /// retained only for explicit compatibility with older devnet deployments.
    pub async fn submit_transfer_legacy_mac(
        &self,
        from_cell: &str,
        to_cell: &str,
        amount: u64,
        signature: &str,
    ) -> Result<String, DevnetError> {
        let url = format!("{}/api/turns/submit", self.base_url);
        let body = serde_json::json!({
            "turn_type": "transfer",
            "from": from_cell,
            "to": to_cell,
            "amount": amount,
            "signature": signature,
        });
        let resp = self.client.post(&url).json(&body).send().await?;
        if !resp.status().is_success() {
            return Err(DevnetError::from_response(resp).await);
        }
        let result: serde_json::Value = resp.json().await?;
        Ok(result["tx_hash"].as_str().unwrap_or("unknown").to_string())
    }

    /// Request tokens from the devnet faucet.
    pub async fn faucet_request(&self, cell_id: &str) -> Result<u64, DevnetError> {
        let url = format!("{}/api/faucet", self.base_url);
        let body = serde_json::json!({
            "recipient": cell_id,
            "amount": 1000,
        });
        let resp = self.client.post(&url).json(&body).send().await?;
        if !resp.status().is_success() {
            return Err(DevnetError::from_response(resp).await);
        }
        let result: FaucetResponse = resp.json().await?;
        if !result.success {
            return Err(DevnetError::Api(
                result
                    .error
                    .unwrap_or_else(|| "faucet request failed".to_string()),
            ));
        }
        Ok(result.amount)
    }

    // ─── Gallery / auction endpoints ───────────────────────────────────────────

    /// List artworks on devnet.
    pub async fn list_artworks(&self) -> Result<Vec<Artwork>, DevnetError> {
        Err(DevnetError::Unsupported(
            "gallery artworks are not exposed by the current public node API",
        ))
    }

    /// List active auctions.
    pub async fn list_auctions(&self) -> Result<Vec<Auction>, DevnetError> {
        Err(DevnetError::Unsupported(
            "gallery auctions are not exposed by the current public node API",
        ))
    }

    /// Place a bid on an auction.
    pub async fn place_bid(
        &self,
        _auction_id: &str,
        _bidder_cell: &str,
        _amount: u64,
        _signature: &str,
    ) -> Result<(), DevnetError> {
        Err(DevnetError::Unsupported(
            "gallery bidding is not exposed by the current public node API",
        ))
    }

    /// Get a user's active bids.
    pub async fn get_user_bids(&self, _cell_id: &str) -> Result<Vec<BidInfo>, DevnetError> {
        Err(DevnetError::Unsupported(
            "gallery bids are not exposed by the current public node API",
        ))
    }

    // ─── Identity / credential endpoints ───────────────────────────────────────

    /// Issue a verifiable credential.
    pub async fn issue_credential(
        &self,
        _issuer_cell: &str,
        _schema: &str,
        _attributes: &str,
        _signature: &str,
    ) -> Result<String, DevnetError> {
        Err(DevnetError::Unsupported(
            "legacy identity issue endpoint is retired; use canonical Starbridge identity actions",
        ))
    }

    /// Request a proof from another user.
    pub async fn request_proof(
        &self,
        _verifier_cell: &str,
        _subject_cell: &str,
        _predicate: &str,
    ) -> Result<ProofRequestResult, DevnetError> {
        Err(DevnetError::Unsupported(
            "identity proof request endpoint is not exposed by the current node read/write API",
        ))
    }

    /// List credentials held by a cell.
    pub async fn list_credentials(
        &self,
        _cell_id: &str,
    ) -> Result<Vec<CredentialInfo>, DevnetError> {
        Err(DevnetError::Unsupported(
            "credential list endpoint is not exposed by the current node read API",
        ))
    }

    // ─── Status / metrics endpoints ────────────────────────────────────────────

    /// Get federation health.
    pub async fn federation_health(&self) -> Result<FederationHealth, DevnetError> {
        let status = self.node_status().await?;
        let is_solo = status.federation_mode == "solo";
        let nodes_total = if is_solo {
            1
        } else {
            status.peer_count.saturating_add(1)
        };
        let nodes_up = if status.healthy { nodes_total } else { 0 };
        Ok(FederationHealth {
            status: if status.healthy {
                "healthy".to_string()
            } else {
                "degraded".to_string()
            },
            nodes_up,
            nodes_total,
            block_height: status.latest_height,
            last_block_time: "n/a".to_string(),
            avg_block_time_ms: 0,
        })
    }

    async fn node_status(&self) -> Result<NodeStatusResponse, DevnetError> {
        let url = format!("{}/status", self.base_url);
        let resp = self.client.get(&url).send().await?;
        if !resp.status().is_success() {
            return Err(DevnetError::from_response(resp).await);
        }
        Ok(resp.json().await?)
    }

    /// Probe the node's `/status` for an operator-facing startup summary. Never
    /// errors out of the call: an unreachable node yields `reachable:false`
    /// with the reason, so the bot can warn loudly but still boot (and recover
    /// once the node comes back).
    pub async fn preflight(&self) -> NodePreflight {
        match self.node_status().await {
            Ok(s) => NodePreflight {
                reachable: true,
                healthy: s.healthy,
                consensus_live: s.consensus_live,
                federation_mode: s.federation_mode,
                dag_height: s.dag_height,
                latest_height: s.latest_height,
                executor_federation_id: s.executor_federation_id,
                error: None,
            },
            Err(e) => NodePreflight {
                reachable: false,
                healthy: false,
                consensus_live: false,
                federation_mode: String::new(),
                dag_height: 0,
                latest_height: 0,
                executor_federation_id: String::new(),
                error: Some(e.to_string()),
            },
        }
    }

    /// The node's current block height (used as the validity-window reference
    /// for CapTP handoff certificates). Returns the node's reported
    /// `latest_height`; the caller decides how to handle the error.
    pub async fn current_height(&self) -> Result<u64, DevnetError> {
        Ok(self.node_status().await?.latest_height)
    }

    /// Verify a STARK proof on-chain.
    pub async fn verify_proof(&self, _proof_hex: &str) -> Result<ProofVerifyResult, DevnetError> {
        Err(DevnetError::Unsupported(
            "proof verification is not exposed by the current public node API",
        ))
    }

    /// Get devnet metrics.
    pub async fn metrics(&self) -> Result<DevnetMetrics, DevnetError> {
        let status = self.node_status().await?;
        let cells_url = format!("{}/api/cells", self.base_url);
        let active_cells = match self.client.get(&cells_url).send().await {
            Ok(resp) if resp.status().is_success() => resp
                .json::<serde_json::Value>()
                .await
                .ok()
                .and_then(|value| value.as_array().map(|cells| cells.len() as u64))
                .unwrap_or(0),
            _ => 0,
        };

        Ok(DevnetMetrics {
            tps: 0.0,
            block_height: status.latest_height,
            pending_turns: 0,
            active_cells,
            memory_usage_mb: 0,
            uptime_secs: 0,
        })
    }

    async fn fetch_receipts(&self) -> Result<Vec<ReceiptInfo>, DevnetError> {
        let url = format!("{}/api/receipts", self.base_url);
        let resp = self.client.get(&url).send().await?;
        if !resp.status().is_success() {
            return Err(DevnetError::from_response(resp).await);
        }
        Ok(resp.json().await?)
    }

    async fn fetch_blocks(&self) -> Result<Vec<AttestedRootInfo>, DevnetError> {
        let url = format!("{}/api/blocks", self.base_url);
        let resp = self.client.get(&url).send().await?;
        if !resp.status().is_success() {
            return Err(DevnetError::from_response(resp).await);
        }
        Ok(resp.json().await?)
    }

    async fn fetch_cells(&self) -> Result<Vec<CellListEntry>, DevnetError> {
        let url = format!("{}/api/cells", self.base_url);
        let resp = self.client.get(&url).send().await?;
        if !resp.status().is_success() {
            return Err(DevnetError::from_response(resp).await);
        }
        Ok(resp.json().await?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn cell_details_accepts_node_explorer_shape() {
        let details: CellDetails = serde_json::from_value(json!({
            "id": "abc123",
            "balance": 42,
            "nonce": 7,
            "capability_count": 3
        }))
        .expect("node /api/cell response should deserialize");

        assert_eq!(details.cell_id, "abc123");
        assert_eq!(details.mode, "hosted");
        assert_eq!(details.balance, 42);
        assert_eq!(details.nonce, 7);
        assert_eq!(details.capabilities_count, 3);
        assert!(details.program_vk.is_none());
    }

    #[test]
    fn node_status_maps_to_federation_health_shape() {
        let status: NodeStatusResponse = serde_json::from_value(json!({
            "healthy": true,
            "peer_count": 0,
            "latest_height": 12,
            "federation_mode": "solo",
            "dag_height": 30400,
            "consensus_live": true,
            "public_key": "9b3512552d162619121bc0fa308b21fee8bc5a34f85fc2d785769d2e82aba9fa",
            "executor_federation_id": "e2986aab050985b671907e0774410a02a593c040b2ba473cf93a44072faf0577"
        }))
        .expect("node /status response should deserialize");

        assert!(status.healthy);
        assert_eq!(status.latest_height, 12);
        assert_eq!(status.federation_mode, "solo");
        // The preflight-relevant fields must round-trip from the real /status.
        assert_eq!(status.dag_height, 30400);
        assert!(status.consensus_live);
        assert_eq!(status.public_key.len(), 64);
        assert_eq!(
            status.executor_federation_id,
            "e2986aab050985b671907e0774410a02a593c040b2ba473cf93a44072faf0577"
        );
    }

    #[test]
    fn user_message_classifies_http_status() {
        let auth = DevnetError::Status {
            code: 403,
            body: String::new(),
        };
        let m = auth.user_message("submit the transfer");
        // ⚑ THE ENV VAR MUST NOT BE IN THE PLAYER'S SENTENCE. It used to be — this test ASSERTED it
        // was, which is how the purest "name a symbol as the fix" instance in the tree survived: the
        // gate was pointed the wrong way. A player cannot set an environment variable on our host.
        assert!(
            !m.contains("DEVNET_API_TOKEN"),
            "a player cannot set an env var; that is the operator's half: {m}"
        );
        assert!(
            m.contains("nothing was changed"),
            "a refusal must say whether anything landed: {m}"
        );
        assert!(
            m.contains("on our side"),
            "the refusal must not blame the player for a permission we hold: {m}"
        );
        // …and the token IS still named, to the audience that can act on it.
        let operator = auth
            .operator_diagnostic()
            .expect("an unauthorized write is an operator condition");
        assert!(operator.contains("DEVNET_API_TOKEN"), "got: {operator}");
        assert!(
            DevnetError::Status {
                code: 429,
                body: String::new(),
            }
            .operator_diagnostic()
            .is_none(),
            "a rate limit is not an operator's misconfiguration"
        );

        let rate = DevnetError::Status {
            code: 429,
            body: String::new(),
        };
        assert!(
            rate.user_message("request faucet tokens")
                .contains("Rate limited")
        );

        let nf = DevnetError::Status {
            code: 404,
            body: String::new(),
        };
        assert!(nf.user_message("query your balance").contains("/faucet"));

        let server = DevnetError::Status {
            code: 503,
            body: String::new(),
        };
        assert!(
            server
                .user_message("cast your vote")
                .contains("node-side fault")
        );
    }

    #[test]
    fn user_message_does_not_leak_html_body() {
        // A misrouted request can return a full HTML page; the hint must skip it.
        let html = DevnetError::Status {
            code: 400,
            body: "<!doctype html><html>big error page</html>".to_string(),
        };
        let m = html.user_message("submit the transfer");
        assert!(!m.contains("<html>"), "HTML body must not leak: {m}");
        assert!(!m.contains("doctype"), "HTML body must not leak: {m}");

        // A short JSON-ish error IS surfaced as a quoted hint.
        let short = DevnetError::Status {
            code: 400,
            body: "nonce too low".to_string(),
        };
        assert!(
            short
                .user_message("submit the transfer")
                .contains("nonce too low")
        );
    }

    #[test]
    fn user_message_surfaces_insufficient_balance() {
        let e = DevnetError::Api("insufficient balance: have 3, need 10".to_string());
        let m = e.user_message("submit the transfer");
        assert!(m.contains("insufficient"), "got: {m}");
        assert!(m.contains("/faucet"), "should suggest topping up: {m}");
    }

    #[test]
    fn committed_events_convert_to_recent_activity() {
        let response = events_response_from_committed(
            vec![
                CommittedEventWire {
                    height: 4,
                    turn_hash: "0123456789abcdef".to_string(),
                    cell_id: "cell-a".to_string(),
                    effects: Vec::new(),
                    timestamp: 100,
                },
                CommittedEventWire {
                    height: 7,
                    turn_hash: "feedfacecafebeef".to_string(),
                    cell_id: "cell-b".to_string(),
                    effects: vec!["signed_turn:2".to_string()],
                    timestamp: 101,
                },
            ],
            3,
        );

        assert_eq!(response.block_height, 7);
        assert_eq!(response.events.len(), 2);
        assert_eq!(response.events[0].summary, "Committed turn 0123456789ab...");
        assert_eq!(response.events[0].cell_id.as_deref(), Some("cell-a"));
        assert_eq!(response.events[1].summary, "signed_turn:2");
        assert_eq!(
            response.events[1].tx_hash.as_deref(),
            Some("feedfacecafebeef")
        );
    }

    #[test]
    fn empty_event_response_preserves_poll_cursor() {
        let response = events_response_from_committed(Vec::new(), 11);

        assert_eq!(response.block_height, 11);
        assert!(response.events.is_empty());
    }
}
