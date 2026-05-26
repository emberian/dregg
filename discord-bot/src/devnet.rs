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
    pub cell_id: String,
    pub mode: String,
    pub balance: u64,
    pub nonce: u64,
    pub capabilities_count: u32,
    pub program_vk: Option<String>,
    pub provenance: Option<String>,
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
        let url = format!("{}/api/events?since={}", self.base_url, since_height);
        let resp = self.client.get(&url).send().await?;
        if !resp.status().is_success() {
            return Err(DevnetError::Api(format!("status {}", resp.status())));
        }
        Ok(resp.json().await?)
    }

    /// Get cell details by ID.
    pub async fn get_cell_details(&self, cell_id: &str) -> Result<CellDetails, DevnetError> {
        let url = format!("{}/api/node/cells/{cell_id}", self.base_url);
        let resp = self.client.get(&url).send().await?;
        if !resp.status().is_success() {
            return Err(DevnetError::Api(format!("status {}", resp.status())));
        }
        Ok(resp.json().await?)
    }

    /// Get turn details by hash.
    pub async fn get_turn_details(&self, turn_hash: &str) -> Result<TurnDetails, DevnetError> {
        let url = format!("{}/api/node/turns/{turn_hash}", self.base_url);
        let resp = self.client.get(&url).send().await?;
        if !resp.status().is_success() {
            return Err(DevnetError::Api(format!("status {}", resp.status())));
        }
        Ok(resp.json().await?)
    }

    /// Get block details by height.
    pub async fn get_block_details(&self, height: u64) -> Result<BlockDetails, DevnetError> {
        let url = format!("{}/api/node/blocks/{height}", self.base_url);
        let resp = self.client.get(&url).send().await?;
        if !resp.status().is_success() {
            return Err(DevnetError::Api(format!("status {}", resp.status())));
        }
        Ok(resp.json().await?)
    }

    /// Get note status by commitment.
    pub async fn get_note_status(&self, commitment: &str) -> Result<NoteStatus, DevnetError> {
        let url = format!("{}/api/node/notes/{commitment}", self.base_url);
        let resp = self.client.get(&url).send().await?;
        if !resp.status().is_success() {
            return Err(DevnetError::Api(format!("status {}", resp.status())));
        }
        Ok(resp.json().await?)
    }

    /// Get proof details by hash.
    pub async fn get_proof_details(&self, hash: &str) -> Result<ProofDetails, DevnetError> {
        let url = format!("{}/api/node/proofs/{hash}", self.base_url);
        let resp = self.client.get(&url).send().await?;
        if !resp.status().is_success() {
            return Err(DevnetError::Api(format!("status {}", resp.status())));
        }
        Ok(resp.json().await?)
    }

    /// Get factory details by VK hash.
    pub async fn get_factory_details(&self, vk_hash: &str) -> Result<FactoryDetails, DevnetError> {
        let url = format!("{}/api/node/factories/{vk_hash}", self.base_url);
        let resp = self.client.get(&url).send().await?;
        if !resp.status().is_success() {
            return Err(DevnetError::Api(format!("status {}", resp.status())));
        }
        Ok(resp.json().await?)
    }

    /// Search for entities by prefix.
    pub async fn explorer_search(&self, query: &str) -> Result<Vec<SearchResult>, DevnetError> {
        let url = format!("{}/api/node/search", self.base_url);
        let resp = self.client.get(&url).query(&[("q", query)]).send().await?;
        if !resp.status().is_success() {
            return Err(DevnetError::Api(format!("status {}", resp.status())));
        }
        Ok(resp.json().await?)
    }

    /// Get explorer stats.
    pub async fn explorer_stats(&self) -> Result<ExplorerStats, DevnetError> {
        let url = format!("{}/api/node/stats", self.base_url);
        let resp = self.client.get(&url).send().await?;
        if !resp.status().is_success() {
            return Err(DevnetError::Api(format!("status {}", resp.status())));
        }
        Ok(resp.json().await?)
    }

    /// Get recent events, optionally filtered by cell_id.
    pub async fn get_recent_events(
        &self,
        count: u32,
        cell_id: Option<&str>,
    ) -> Result<Vec<RecentEvent>, DevnetError> {
        let url = format!("{}/api/node/events/recent", self.base_url);
        let mut req = self.client.get(&url).query(&[("count", count.to_string())]);
        if let Some(cid) = cell_id {
            req = req.query(&[("cell_id", cid.to_string())]);
        }
        let resp = req.send().await?;
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
        let url = format!("{}/api/cells/register", self.base_url);
        let body = serde_json::json!({
            "cell_id": cell_id,
            "public_key": public_key,
            "mode": "hosted",
        });
        let resp = self.client.post(&url).json(&body).send().await?;
        if !resp.status().is_success() {
            let msg = resp.text().await.unwrap_or_default();
            return Err(DevnetError::Api(msg));
        }
        Ok(())
    }

    /// Get the balance of a cell.
    pub async fn get_balance(&self, cell_id: &str) -> Result<u64, DevnetError> {
        let url = format!("{}/api/node/cells/{cell_id}", self.base_url);
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
        let body = serde_json::json!({ "cell_id": cell_id });
        let resp = self.client.post(&url).json(&body).send().await?;
        if !resp.status().is_success() {
            let msg = resp.text().await.unwrap_or_default();
            return Err(DevnetError::Api(msg));
        }
        let result: serde_json::Value = resp.json().await?;
        Ok(result["amount"].as_u64().unwrap_or(1000))
    }

    // ─── Gallery / auction endpoints ───────────────────────────────────────────

    /// List artworks on devnet.
    pub async fn list_artworks(&self) -> Result<Vec<Artwork>, DevnetError> {
        let url = format!("{}/api/gallery/artworks", self.base_url);
        let resp = self.client.get(&url).send().await?;
        if !resp.status().is_success() {
            return Err(DevnetError::Api(format!("status {}", resp.status())));
        }
        Ok(resp.json().await?)
    }

    /// List active auctions.
    pub async fn list_auctions(&self) -> Result<Vec<Auction>, DevnetError> {
        let url = format!("{}/api/gallery/auctions", self.base_url);
        let resp = self.client.get(&url).send().await?;
        if !resp.status().is_success() {
            return Err(DevnetError::Api(format!("status {}", resp.status())));
        }
        Ok(resp.json().await?)
    }

    /// Place a bid on an auction.
    pub async fn place_bid(
        &self,
        auction_id: &str,
        bidder_cell: &str,
        amount: u64,
        signature: &str,
    ) -> Result<(), DevnetError> {
        let url = format!("{}/api/gallery/auctions/{auction_id}/bid", self.base_url);
        let body = serde_json::json!({
            "bidder": bidder_cell,
            "amount": amount,
            "signature": signature,
        });
        let resp = self.client.post(&url).json(&body).send().await?;
        if !resp.status().is_success() {
            let msg = resp.text().await.unwrap_or_default();
            return Err(DevnetError::Api(msg));
        }
        Ok(())
    }

    /// Get a user's active bids.
    pub async fn get_user_bids(&self, cell_id: &str) -> Result<Vec<BidInfo>, DevnetError> {
        let url = format!("{}/api/gallery/bids", self.base_url);
        let resp = self
            .client
            .get(&url)
            .query(&[("cell_id", cell_id)])
            .send()
            .await?;
        if !resp.status().is_success() {
            return Err(DevnetError::Api(format!("status {}", resp.status())));
        }
        Ok(resp.json().await?)
    }

    // ─── Identity / credential endpoints ───────────────────────────────────────

    /// Issue a verifiable credential.
    pub async fn issue_credential(
        &self,
        issuer_cell: &str,
        schema: &str,
        attributes: &str,
        signature: &str,
    ) -> Result<String, DevnetError> {
        let url = format!("{}/api/identity/credentials/issue", self.base_url);
        let body = serde_json::json!({
            "issuer": issuer_cell,
            "schema": schema,
            "attributes": attributes,
            "signature": signature,
        });
        let resp = self.client.post(&url).json(&body).send().await?;
        if !resp.status().is_success() {
            let msg = resp.text().await.unwrap_or_default();
            return Err(DevnetError::Api(msg));
        }
        let result: serde_json::Value = resp.json().await?;
        Ok(result["credential_id"]
            .as_str()
            .unwrap_or("unknown")
            .to_string())
    }

    /// Request a proof from another user.
    pub async fn request_proof(
        &self,
        verifier_cell: &str,
        subject_cell: &str,
        predicate: &str,
    ) -> Result<ProofRequestResult, DevnetError> {
        let url = format!("{}/api/identity/proofs/request", self.base_url);
        let body = serde_json::json!({
            "verifier": verifier_cell,
            "subject": subject_cell,
            "predicate": predicate,
        });
        let resp = self.client.post(&url).json(&body).send().await?;
        if !resp.status().is_success() {
            let msg = resp.text().await.unwrap_or_default();
            return Err(DevnetError::Api(msg));
        }
        Ok(resp.json().await?)
    }

    /// List credentials held by a cell.
    pub async fn list_credentials(
        &self,
        cell_id: &str,
    ) -> Result<Vec<CredentialInfo>, DevnetError> {
        let url = format!("{}/api/identity/credentials", self.base_url);
        let resp = self
            .client
            .get(&url)
            .query(&[("cell_id", cell_id)])
            .send()
            .await?;
        if !resp.status().is_success() {
            return Err(DevnetError::Api(format!("status {}", resp.status())));
        }
        Ok(resp.json().await?)
    }

    // ─── Status / metrics endpoints ────────────────────────────────────────────

    /// Get federation health.
    pub async fn federation_health(&self) -> Result<FederationHealth, DevnetError> {
        let url = format!("{}/api/node/health", self.base_url);
        let resp = self.client.get(&url).send().await?;
        if !resp.status().is_success() {
            return Err(DevnetError::Api(format!("status {}", resp.status())));
        }
        Ok(resp.json().await?)
    }

    /// Verify a STARK proof on-chain.
    pub async fn verify_proof(&self, proof_hex: &str) -> Result<ProofVerifyResult, DevnetError> {
        let url = format!("{}/api/node/proofs/verify", self.base_url);
        let body = serde_json::json!({ "proof": proof_hex });
        let resp = self.client.post(&url).json(&body).send().await?;
        if !resp.status().is_success() {
            let msg = resp.text().await.unwrap_or_default();
            return Err(DevnetError::Api(msg));
        }
        Ok(resp.json().await?)
    }

    /// Get devnet metrics.
    pub async fn metrics(&self) -> Result<DevnetMetrics, DevnetError> {
        let url = format!("{}/api/node/metrics", self.base_url);
        let resp = self.client.get(&url).send().await?;
        if !resp.status().is_success() {
            return Err(DevnetError::Api(format!("status {}", resp.status())));
        }
        Ok(resp.json().await?)
    }
}
