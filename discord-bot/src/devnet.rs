//! Client for the dregg devnet API.

use crate::cipherclerk::UserCipherclerk;
use dregg_sdk::SignedTurn;
use dregg_turn::Action;
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
    pub executor_signed: bool,
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
    Api(String),
    Unsupported(&'static str),
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
            let msg = resp.text().await.unwrap_or_default();
            return Err(DevnetError::Api(msg));
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

    async fn fetch_cell_nonce(&self, cell_id: &str) -> Result<u64, DevnetError> {
        let url = format!("{}/api/cell/{cell_id}", self.base_url);
        let resp = self.client.get(&url).send().await?;
        if !resp.status().is_success() {
            return Err(DevnetError::Api(format!("status {}", resp.status())));
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
            return Err(DevnetError::Api(format!("status {}", resp.status())));
        }
        let events: Vec<CommittedEventWire> = resp.json().await?;
        Ok(events_response_from_committed(events, since_height))
    }

    /// Get cell details by ID.
    pub async fn get_cell_details(&self, cell_id: &str) -> Result<CellDetails, DevnetError> {
        let url = format!("{}/api/cell/{cell_id}", self.base_url);
        let resp = self.client.get(&url).send().await?;
        if !resp.status().is_success() {
            return Err(DevnetError::Api(format!("status {}", resp.status())));
        }
        Ok(resp.json().await?)
    }

    /// Get turn details by hash.
    pub async fn get_turn_details(&self, turn_hash: &str) -> Result<TurnDetails, DevnetError> {
        let url = format!("{}/api/receipts", self.base_url);
        let resp = self.client.get(&url).send().await?;
        if !resp.status().is_success() {
            return Err(DevnetError::Api(format!("status {}", resp.status())));
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
            proof_type: if receipt.executor_signed || receipt.has_proof {
                "executor-signed receipt".to_string()
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
            return Err(DevnetError::Api(format!("status {}", resp.status())));
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
                        "balance {} PYN, nonce {}, {} capability(s)",
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
                        "{} action(s), {}, chain index {}{}",
                        receipt.action_count,
                        receipt.finality,
                        receipt.chain_index,
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
            return Err(DevnetError::Api(format!("status {}", resp.status())));
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
            return Err(DevnetError::Api(format!("status {}", resp.status())));
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
            return Err(DevnetError::Api(format!("status {}", resp.status())));
        }
        Ok(resp.json().await?)
    }

    /// Get the explorer base URL for building links.
    pub fn explorer_base_url(&self) -> &'static str {
        "https://devnet.dregg.fg-goose.online/explorer"
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
            let msg = resp.text().await.unwrap_or_default();
            return Err(DevnetError::Api(msg));
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
            return Err(DevnetError::Api(format!("status {}", resp.status())));
        }
        let cell: CellDetails = resp.json().await?;
        Ok(cell.balance)
    }

    /// Submit a transfer between two cells.
    pub async fn submit_transfer(
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
            let msg = resp.text().await.unwrap_or_default();
            return Err(DevnetError::Api(msg));
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
            let msg = resp.text().await.unwrap_or_default();
            return Err(DevnetError::Api(msg));
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
            return Err(DevnetError::Api(format!("status {}", resp.status())));
        }
        Ok(resp.json().await?)
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
            return Err(DevnetError::Api(format!("status {}", resp.status())));
        }
        Ok(resp.json().await?)
    }

    async fn fetch_blocks(&self) -> Result<Vec<AttestedRootInfo>, DevnetError> {
        let url = format!("{}/api/blocks", self.base_url);
        let resp = self.client.get(&url).send().await?;
        if !resp.status().is_success() {
            return Err(DevnetError::Api(format!("status {}", resp.status())));
        }
        Ok(resp.json().await?)
    }

    async fn fetch_cells(&self) -> Result<Vec<CellListEntry>, DevnetError> {
        let url = format!("{}/api/cells", self.base_url);
        let resp = self.client.get(&url).send().await?;
        if !resp.status().is_success() {
            return Err(DevnetError::Api(format!("status {}", resp.status())));
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
            "public_key": "ignored"
        }))
        .expect("node /status response should deserialize");

        assert!(status.healthy);
        assert_eq!(status.latest_height, 12);
        assert_eq!(status.federation_mode, "solo");
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
