//! Client for the pyana devnet API.

use serde::Deserialize;

/// Client for communicating with the pyana devnet.
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
    pub amm_tvl: u64,
    pub active_orders: u64,
    pub open_cdps: u64,
    pub federation_nodes_up: u32,
    pub federation_nodes_total: u32,
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
        Self {
            base_url: base_url.trim_end_matches('/').to_string(),
            client: reqwest::Client::builder()
                .timeout(std::time::Duration::from_secs(10))
                .build()
                .expect("failed to build HTTP client"),
        }
    }

    /// Get events since a given block height (for the activity feed poller).
    pub async fn get_events_since(
        &self,
        since_height: u64,
    ) -> Result<EventsResponse, DevnetError> {
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
        let resp = self
            .client
            .get(&url)
            .query(&[("q", query)])
            .send()
            .await?;
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
        "https://devnet.pyana.fg-goose.online/explorer"
    }
}
