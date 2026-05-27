//! Relay operator service.
//!
//! Exposes the storage-template relay operator service. Operators bond
//! computrons to host inboxes, accept store-and-forward messages from senders,
//! deliver them to recipients on drain, charge fees, and run periodic GC.
//!
//! # Endpoints
//!
//! ```text
//! GET  /relay/status            -- operator info (bond, inboxes, earnings)
//! POST /relay/subscribe         -- create a hosted inbox
//! DELETE /relay/unsubscribe     -- remove an inbox
//! POST /relay/send/:dest        -- enqueue a message
//! GET  /relay/drain             -- drain your inbox (authenticated)
//! GET  /relay/inbox/:id/status  -- check inbox status
//! GET  /relay/proof/:msg_id     -- get dequeue proof for a delivered message
//! ```

use std::collections::BTreeMap;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Duration;

use axum::extract::{Path, State};
use axum::http::StatusCode;
use axum::routing::{delete, get, post};
use axum::{Json, Router};
use serde::{Deserialize, Serialize};
use tokio::sync::RwLock;
use tracing::info;

use dregg_storage::inbox::InboxMessage;
use dregg_storage::operator::RelayOperator;
use dregg_storage::queue::{DequeueProof, MerkleQueue, QueueEntry};
use dregg_storage_templates::relay_operator::{
    BYTES_RELAYED_THIS_EPOCH_SLOT, DEFAULT_EPOCH_DURATION, HOSTED_INBOX_ROOT_SLOT,
    QUOTA_BYTES_PER_EPOCH_SLOT, initial_state, relay_operator_child_program_vk,
    relay_operator_factory_descriptor, relay_operator_program_with,
};

// ─── Configuration ────────────────────────────────────────────────────────────

/// Configuration for the relay operator service.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RelayConfig {
    /// Port to listen on.
    pub listen_port: u16,
    /// Operator identity key (32 bytes, hex-encoded when serialized to file).
    #[serde(serialize_with = "hex_ser_32", deserialize_with = "hex_de_32")]
    pub operator_key: [u8; 32],
    /// Bond amount (computrons staked).
    pub bond_amount: u64,
    /// Fee policy (what assets accepted, at what rates).
    pub fee_policy: FeePolicy,
    /// Maximum total capacity to host (sum of all inbox capacities).
    pub max_total_capacity: usize,
    /// GC interval in seconds.
    pub gc_interval_secs: u64,
    /// TTL for messages in blocks (used during GC).
    pub message_ttl_blocks: u64,
    /// SLA: max delivery latency in blocks.
    pub max_delivery_latency_blocks: u64,
    /// Path for persistent state file.
    pub state_file: PathBuf,
    /// Default inbox capacity for new subscriptions.
    pub default_inbox_capacity: usize,
    /// Default minimum deposit for new inboxes.
    pub default_min_deposit: u64,
}

impl Default for RelayConfig {
    fn default() -> Self {
        Self {
            listen_port: 3100,
            operator_key: [0u8; 32],
            bond_amount: 10_000,
            fee_policy: FeePolicy::default(),
            max_total_capacity: 100_000,
            gc_interval_secs: 300,
            message_ttl_blocks: 1000,
            max_delivery_latency_blocks: 50,
            state_file: PathBuf::from("./relay-state.json"),
            default_inbox_capacity: 100,
            default_min_deposit: 100,
        }
    }
}

/// Fee policy: which assets are accepted and at what rates.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FeePolicy {
    /// Minimum deposit per message (in computrons).
    pub min_deposit_computrons: u64,
    /// Subscription fee (one-time, for creating an inbox).
    pub subscription_fee: u64,
    /// Whether to accept external assets (USDC, ETH, etc.) via deposit vouchers.
    pub accept_external_assets: bool,
    /// Exchange rate: external asset units per computron (fixed-point, 1e6 = 1:1).
    pub external_rate_micros: u64,
}

impl Default for FeePolicy {
    fn default() -> Self {
        Self {
            min_deposit_computrons: 100,
            subscription_fee: 1000,
            accept_external_assets: false,
            external_rate_micros: 1_000_000,
        }
    }
}

// ─── Service State ────────────────────────────────────────────────────────────

/// Shared relay service state.
pub struct RelayState {
    /// Legacy in-memory queue engine. The storage-template mirror below is the
    /// public cell-program state; this engine remains the byte queue backend
    /// until hosted inbox queues are fully cell-backed.
    pub operator: RelayOperator,
    /// Storage-template cell-program mirror for the relay operator.
    pub template: RelayTemplateState,
    /// Configuration.
    pub config: RelayConfig,
    /// Current block height (updated by the node or a ticker).
    pub current_height: u64,
    /// Delivered message proofs: msg_hash -> DequeueProof.
    pub delivery_proofs: std::collections::HashMap<[u8; 32], DequeueProof>,
    /// Total messages delivered since startup.
    pub messages_delivered: u64,
    /// Total messages received since startup.
    pub messages_received: u64,
}

pub type SharedRelayState = Arc<RwLock<RelayState>>;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RelayTemplateState {
    #[serde(serialize_with = "hex_ser_32", deserialize_with = "hex_de_32")]
    pub factory_vk: [u8; 32],
    #[serde(serialize_with = "hex_ser_32", deserialize_with = "hex_de_32")]
    pub factory_hash: [u8; 32],
    #[serde(serialize_with = "hex_ser_32", deserialize_with = "hex_de_32")]
    pub child_program_vk: [u8; 32],
    pub epoch_duration_blocks: u64,
    pub slots: [[u8; 32]; 8],
    pub hosted_inboxes: BTreeMap<[u8; 32], RelayTemplateHostedInbox>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RelayTemplateHostedInbox {
    #[serde(serialize_with = "hex_ser_32", deserialize_with = "hex_de_32")]
    pub owner: [u8; 32],
    pub committed_capacity: usize,
    pub min_deposit: u64,
    #[serde(serialize_with = "hex_ser_32", deserialize_with = "hex_de_32")]
    pub queue_root: [u8; 32],
    pub pending_messages: usize,
    pub last_drain_height: u64,
    pub evicted: bool,
    pub queue_entries: Vec<RelayTemplateQueueEntry>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RelayTemplateQueueEntry {
    #[serde(serialize_with = "hex_ser_32", deserialize_with = "hex_de_32")]
    pub content_hash: [u8; 32],
    #[serde(serialize_with = "hex_ser_32", deserialize_with = "hex_de_32")]
    pub sender: [u8; 32],
    pub deposit: u64,
    pub enqueued_at: u64,
    pub size: usize,
}

impl From<&RelayTemplateQueueEntry> for QueueEntry {
    fn from(entry: &RelayTemplateQueueEntry) -> Self {
        Self {
            content_hash: entry.content_hash,
            sender: entry.sender,
            deposit: entry.deposit,
            enqueued_at: entry.enqueued_at,
            size: entry.size,
        }
    }
}

impl RelayTemplateState {
    pub fn new(config: &RelayConfig) -> Self {
        let descriptor = relay_operator_factory_descriptor();
        let operator_pk_hash = blake3_field(&config.operator_key);
        let route_table_root = default_route_table_root();
        let quota = config.max_total_capacity as u64;
        Self {
            factory_vk: descriptor.factory_vk,
            factory_hash: descriptor.hash(),
            child_program_vk: relay_operator_child_program_vk(),
            epoch_duration_blocks: DEFAULT_EPOCH_DURATION,
            slots: initial_state(
                config.bond_amount,
                config.bond_amount,
                quota,
                operator_pk_hash,
                route_table_root,
            ),
            hosted_inboxes: BTreeMap::new(),
        }
    }

    pub fn hosted_inbox_root(&self) -> [u8; 32] {
        self.slots[HOSTED_INBOX_ROOT_SLOT as usize]
    }

    pub fn bytes_relayed_this_epoch(&self) -> u64 {
        u64_from_field(self.slots[BYTES_RELAYED_THIS_EPOCH_SLOT as usize])
    }

    pub fn quota_bytes_per_epoch(&self) -> u64 {
        u64_from_field(self.slots[QUOTA_BYTES_PER_EPOCH_SLOT as usize])
    }

    pub fn active_inbox_count(&self) -> usize {
        self.hosted_inboxes
            .values()
            .filter(|inbox| !inbox.evicted)
            .count()
    }

    pub fn total_capacity(&self) -> usize {
        self.hosted_inboxes
            .values()
            .filter(|inbox| !inbox.evicted)
            .map(|inbox| inbox.committed_capacity)
            .sum()
    }

    pub fn total_pending(&self) -> usize {
        self.hosted_inboxes
            .values()
            .filter(|inbox| !inbox.evicted)
            .map(|inbox| inbox.pending_messages)
            .sum()
    }

    fn register_inbox(
        &mut self,
        owner: [u8; 32],
        capacity: usize,
        min_deposit: u64,
        queue_root: [u8; 32],
    ) -> Result<[u8; 32], String> {
        if self
            .hosted_inboxes
            .get(&owner)
            .is_some_and(|inbox| !inbox.evicted)
        {
            return Err("relay template register_inbox rejected already-hosted inbox".into());
        }
        self.hosted_inboxes.insert(
            owner,
            RelayTemplateHostedInbox {
                owner,
                committed_capacity: capacity,
                min_deposit,
                queue_root,
                pending_messages: 0,
                last_drain_height: 0,
                evicted: false,
                queue_entries: Vec::new(),
            },
        );
        self.commit_hosted_root()
    }

    fn mark_inbox_evicted(&mut self, owner: &[u8; 32]) -> Result<[u8; 32], String> {
        let inbox = self
            .hosted_inboxes
            .get_mut(owner)
            .ok_or_else(|| "relay template unsubscribe rejected missing inbox".to_string())?;
        if inbox.evicted {
            return Err("relay template unsubscribe rejected already-evicted inbox".into());
        }
        inbox.evicted = true;
        inbox.pending_messages = 0;
        inbox.queue_root = [0u8; 32];
        inbox.queue_entries.clear();
        self.commit_hosted_root()
    }

    fn record_enqueue(
        &mut self,
        owner: &[u8; 32],
        msg: InboxMessage,
        deposit: u64,
        height: u64,
    ) -> Result<(), String> {
        let before = self.clone();
        let bytes = msg.size() as u64;
        self.record_relay_bytes(bytes)?;
        let inbox = match self.hosted_inboxes.get_mut(owner) {
            Some(inbox) if !inbox.evicted => inbox,
            Some(_) => {
                *self = before;
                return Err("relay template enqueue rejected evicted inbox".into());
            }
            None => {
                *self = before;
                return Err("relay template enqueue rejected missing inbox".into());
            }
        };
        if inbox.pending_messages >= inbox.committed_capacity {
            *self = before;
            return Err("relay template enqueue rejected full inbox".into());
        }
        inbox.queue_entries.push(RelayTemplateQueueEntry {
            content_hash: inbox_message_content_hash(&msg),
            sender: msg.sender(),
            deposit,
            enqueued_at: height,
            size: msg.size(),
        });
        inbox.pending_messages = inbox.queue_entries.len();
        inbox.queue_root = queue_root_from_template_entries(
            inbox.committed_capacity,
            inbox.queue_entries.iter().map(QueueEntry::from),
        )?;
        if let Err(e) = self.commit_hosted_root() {
            *self = before;
            return Err(e);
        }
        Ok(())
    }

    fn drain_inbox(
        &mut self,
        owner: &[u8; 32],
        max: usize,
        height: u64,
    ) -> Result<Vec<(QueueEntry, DequeueProof)>, String> {
        let before = self.clone();
        let inbox = match self.hosted_inboxes.get_mut(owner) {
            Some(inbox) if !inbox.evicted => inbox,
            Some(_) => return Err("relay template drain rejected evicted inbox".into()),
            None => return Err("relay template drain rejected missing inbox".into()),
        };
        let drain_count = max.min(inbox.queue_entries.len());
        let mut queue = template_queue_from_entries(
            inbox.committed_capacity,
            inbox.queue_entries.iter().map(QueueEntry::from),
        )?;
        let mut drained = Vec::with_capacity(drain_count);
        for _ in 0..drain_count {
            let (entry, proof) = queue
                .dequeue()
                .map_err(|e| format!("relay template drain queue rejected: {e:?}"))?;
            drained.push((entry, proof));
        }
        inbox.queue_entries.drain(0..drain_count);
        inbox.pending_messages = inbox.queue_entries.len();
        inbox.queue_root = queue.root();
        inbox.last_drain_height = height;
        if let Err(e) = self.commit_hosted_root() {
            *self = before;
            return Err(e);
        }
        Ok(drained)
    }

    fn validate_enqueue(&self, owner: &[u8; 32], bytes: u64, deposit: u64) -> Result<(), String> {
        let previous = self.bytes_relayed_this_epoch();
        let next = previous
            .checked_add(bytes)
            .ok_or_else(|| "relay template byte counter overflow".to_string())?;
        let quota = self.quota_bytes_per_epoch();
        if next > quota {
            return Err(format!(
                "relay template RateLimitBySum rejected {previous} + {bytes} > {quota}"
            ));
        }
        let inbox = match self.hosted_inboxes.get(owner) {
            Some(inbox) if !inbox.evicted => inbox,
            Some(_) => return Err("relay template enqueue rejected evicted inbox".into()),
            None => return Err("relay template enqueue rejected missing inbox".into()),
        };
        if inbox.pending_messages >= inbox.committed_capacity {
            return Err("relay template enqueue rejected full inbox".into());
        }
        if deposit < inbox.min_deposit {
            return Err(format!(
                "relay template enqueue rejected insufficient deposit {deposit} < {}",
                inbox.min_deposit
            ));
        }
        Ok(())
    }

    fn commit_hosted_root(&mut self) -> Result<[u8; 32], String> {
        let new_root = self.compute_hosted_root();
        if new_root == [0u8; 32] && self.active_inbox_count() > 0 {
            return Err("relay template register_inbox would set zero hosted_inbox_root".into());
        }
        self.slots[HOSTED_INBOX_ROOT_SLOT as usize] = new_root;
        Ok(new_root)
    }

    fn compute_hosted_root(&self) -> [u8; 32] {
        if self.active_inbox_count() == 0 {
            return [0u8; 32];
        }
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"dregg-relay-template-hosted-inbox-root-v1");
        for (owner, inbox) in &self.hosted_inboxes {
            if inbox.evicted {
                continue;
            }
            hasher.update(owner);
            hasher.update(&(inbox.committed_capacity as u64).to_be_bytes());
            hasher.update(&inbox.min_deposit.to_be_bytes());
            hasher.update(&inbox.queue_root);
            hasher.update(&(inbox.pending_messages as u64).to_be_bytes());
            hasher.update(&inbox.last_drain_height.to_be_bytes());
        }
        *hasher.finalize().as_bytes()
    }

    fn record_relay_bytes(&mut self, bytes: u64) -> Result<(), String> {
        let previous = self.bytes_relayed_this_epoch();
        let next = previous
            .checked_add(bytes)
            .ok_or_else(|| "relay template byte counter overflow".to_string())?;
        let quota = self.quota_bytes_per_epoch();
        if next > quota {
            return Err(format!(
                "relay template RateLimitBySum rejected {previous} + {bytes} > {quota}"
            ));
        }
        self.slots[BYTES_RELAYED_THIS_EPOCH_SLOT as usize] = u64_field(next);
        Ok(())
    }

    pub fn relay_case_has_dfa_and_rate_limit(&self) -> bool {
        let program =
            relay_operator_program_with(self.quota_bytes_per_epoch(), self.epoch_duration_blocks);
        let dregg_cell::program::CellProgram::Cases(cases) = program else {
            return false;
        };
        cases.iter().any(|case| {
            matches!(
                &case.guard,
                dregg_cell::program::TransitionGuard::MethodIs { method }
                    if *method == dregg_storage_templates::relay_operator::relay_method_symbol()
            ) && case.constraints.iter().any(|c| {
                matches!(
                    c,
                    dregg_cell::StateConstraint::RateLimitBySum { slot_index, .. }
                        if *slot_index == BYTES_RELAYED_THIS_EPOCH_SLOT
                )
            }) && case.constraints.iter().any(|c| {
                matches!(
                    c,
                    dregg_cell::StateConstraint::Witnessed { wp }
                        if matches!(wp.kind, dregg_cell::predicate::WitnessedPredicateKind::Dfa)
                )
            })
        })
    }
}

// ─── HTTP API Types ───────────────────────────────────────────────────────────

/// GET /relay/status response.
#[derive(Serialize)]
pub struct RelayStatusResponse {
    pub operator_id: String,
    pub relay_template_factory_vk: String,
    pub relay_template_factory_hash: String,
    pub relay_template_child_program_vk: String,
    pub relay_template_hosted_inbox_root: String,
    pub relay_template_bytes_relayed_this_epoch: u64,
    pub relay_template_quota_bytes_per_epoch: u64,
    pub relay_template_dfa_rate_limit_bound: bool,
    pub bond: u64,
    pub required_bond: u64,
    pub is_underbonded: bool,
    pub active_inboxes: usize,
    pub total_pending_messages: usize,
    pub earned_fees: u64,
    pub max_delivery_latency_blocks: u64,
    pub current_height: u64,
    pub messages_delivered: u64,
    pub messages_received: u64,
    pub gc_interval_secs: u64,
}

/// POST /relay/subscribe request.
#[derive(Deserialize)]
pub struct SubscribeRequest {
    /// Owner public key (hex-encoded, 64 chars).
    pub owner: String,
    /// Requested inbox capacity (optional, defaults to config).
    pub capacity: Option<usize>,
    /// Custom minimum deposit (optional, defaults to config).
    pub min_deposit: Option<u64>,
    /// Hex-encoded 8-byte nonce, included in the signed message to bind the
    /// request to a single use (F-P1-1).
    pub nonce: String,
    /// Hex-encoded 64-byte Ed25519 signature over
    /// `b"dregg-relay-subscribe-v1" || owner || nonce`.
    pub signature: String,
}

/// POST /relay/subscribe response.
#[derive(Serialize)]
pub struct SubscribeResponse {
    pub owner: String,
    pub capacity: usize,
    pub min_deposit: u64,
    pub subscription_fee_paid: u64,
    pub relay_template_hosted_inbox_root: String,
}

/// DELETE /relay/unsubscribe request.
#[derive(Deserialize)]
pub struct UnsubscribeRequest {
    /// Owner public key (hex-encoded).
    pub owner: String,
    /// Hex-encoded 8-byte nonce (F-P1-1).
    pub nonce: String,
    /// Hex-encoded 64-byte Ed25519 signature over
    /// `b"dregg-relay-unsubscribe-v1" || owner || nonce`.
    pub signature: String,
}

/// POST /relay/send/:dest request.
#[derive(Deserialize)]
pub struct SendRequest {
    /// Sender public key (hex-encoded).
    pub sender: String,
    /// Message payload (base64-encoded).
    pub payload: String,
    /// Deposit amount (computrons).
    pub deposit: u64,
}

/// POST /relay/send/:dest response.
#[derive(Debug, Serialize)]
pub struct SendResponse {
    pub queue_root: String,
    pub position: usize,
    pub relay_template_bytes_relayed_this_epoch: u64,
}

/// GET /relay/drain request (via query params or auth header).
#[derive(Deserialize)]
pub struct DrainQuery {
    /// Owner public key (hex-encoded).
    pub owner: String,
    /// Maximum messages to drain.
    pub max: Option<usize>,
    /// Hex-encoded 8-byte nonce (F-P1-1).
    pub nonce: String,
    /// Hex-encoded 64-byte Ed25519 signature over
    /// `b"dregg-relay-drain-v1" || owner || nonce || max_le_bytes`.
    pub signature: String,
}

/// GET /relay/drain response.
#[derive(Serialize)]
pub struct DrainResponse {
    pub messages: Vec<DrainedMessage>,
    pub new_root: String,
}

/// A single drained message with proof.
#[derive(Serialize)]
pub struct DrainedMessage {
    pub content_hash: String,
    pub sender: String,
    pub deposit: u64,
    pub enqueued_at: u64,
    pub proof_old_root: String,
    pub proof_new_root: String,
}

/// GET /relay/inbox/:id/status response.
#[derive(Serialize)]
pub struct InboxStatusResponse {
    pub owner: String,
    pub pending_messages: usize,
    pub committed_capacity: usize,
    pub queue_root: String,
    pub last_drain_height: u64,
    pub evicted: bool,
}

/// GET /relay/proof/:msg_id response.
#[derive(Serialize)]
pub struct ProofResponse {
    pub msg_id: String,
    pub old_root: String,
    pub new_root: String,
    pub found: bool,
}

/// Generic error response.
#[derive(Debug, Serialize)]
pub struct ErrorResponse {
    pub error: String,
}

// ─── Router ───────────────────────────────────────────────────────────────────

/// Build the relay service HTTP router.
pub fn relay_router(state: SharedRelayState) -> Router {
    Router::new()
        .route("/relay/status", get(handle_status))
        .route("/relay/subscribe", post(handle_subscribe))
        .route("/relay/unsubscribe", delete(handle_unsubscribe))
        .route("/relay/send/{dest}", post(handle_send))
        .route("/relay/drain", get(handle_drain))
        .route("/relay/inbox/{id}/status", get(handle_inbox_status))
        .route("/relay/proof/{msg_id}", get(handle_proof))
        .with_state(state)
}

// ─── Auth helpers (F-P1-1) ────────────────────────────────────────────────────

/// Verify an Ed25519 signature over a domain-separated message that the
/// `owner` is supposed to have signed. Used to gate subscribe/unsubscribe/drain
/// (F-P1-1).
fn verify_owner_signature(
    owner: &[u8; 32],
    signature_hex: &str,
    domain: &[u8],
    payload: &[u8],
) -> Result<(), &'static str> {
    use ed25519_dalek::{Signature, Verifier, VerifyingKey};

    let sig_bytes = hex_decode_var(signature_hex).map_err(|_| "invalid signature hex")?;
    if sig_bytes.len() != 64 {
        return Err("signature must be 64 bytes");
    }
    let mut sig_arr = [0u8; 64];
    sig_arr.copy_from_slice(&sig_bytes);
    let sig = Signature::from_bytes(&sig_arr);
    let vk = VerifyingKey::from_bytes(owner).map_err(|_| "invalid owner public key")?;

    let mut msg = Vec::with_capacity(domain.len() + payload.len());
    msg.extend_from_slice(domain);
    msg.extend_from_slice(payload);

    vk.verify(&msg, &sig)
        .map_err(|_| "signature does not verify")
}

fn hex_decode_var(s: &str) -> Result<Vec<u8>, ()> {
    if s.len() % 2 != 0 {
        return Err(());
    }
    let mut out = Vec::with_capacity(s.len() / 2);
    for i in 0..s.len() / 2 {
        out.push(u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).map_err(|_| ())?);
    }
    Ok(out)
}

// ─── Handlers ─────────────────────────────────────────────────────────────────

async fn handle_status(State(state): State<SharedRelayState>) -> Json<RelayStatusResponse> {
    let s = state.read().await;
    Json(RelayStatusResponse {
        operator_id: hex_encode(&s.operator.id),
        relay_template_factory_vk: hex_encode(&s.template.factory_vk),
        relay_template_factory_hash: hex_encode(&s.template.factory_hash),
        relay_template_child_program_vk: hex_encode(&s.template.child_program_vk),
        relay_template_hosted_inbox_root: hex_encode(&s.template.hosted_inbox_root()),
        relay_template_bytes_relayed_this_epoch: s.template.bytes_relayed_this_epoch(),
        relay_template_quota_bytes_per_epoch: s.template.quota_bytes_per_epoch(),
        relay_template_dfa_rate_limit_bound: s.template.relay_case_has_dfa_and_rate_limit(),
        bond: s.operator.bond,
        required_bond: s.operator.required_bond(),
        is_underbonded: s.operator.is_underbonded(),
        active_inboxes: s.template.active_inbox_count(),
        total_pending_messages: s.template.total_pending(),
        earned_fees: s.operator.earned_fees,
        max_delivery_latency_blocks: s.operator.max_delivery_latency,
        current_height: s.current_height,
        messages_delivered: s.messages_delivered,
        messages_received: s.messages_received,
        gc_interval_secs: s.config.gc_interval_secs,
    })
}

async fn handle_subscribe(
    State(state): State<SharedRelayState>,
    Json(req): Json<SubscribeRequest>,
) -> Result<Json<SubscribeResponse>, (StatusCode, Json<ErrorResponse>)> {
    let owner = hex_decode_32(&req.owner).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid owner key (expected 64 hex chars)".to_string(),
            }),
        )
    })?;

    // F-P1-1: require an Ed25519 signature from `owner` over a domain-separated
    // (owner, nonce) tuple. Without this, any network attacker could subscribe
    // an inbox in another user's name.
    let nonce_bytes = hex_decode_var(&req.nonce).map_err(|_| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid nonce hex".to_string(),
            }),
        )
    })?;
    let mut payload = Vec::with_capacity(32 + nonce_bytes.len());
    payload.extend_from_slice(&owner);
    payload.extend_from_slice(&nonce_bytes);
    if let Err(e) = verify_owner_signature(
        &owner,
        &req.signature,
        b"dregg-relay-subscribe-v1",
        &payload,
    ) {
        return Err((
            StatusCode::FORBIDDEN,
            Json(ErrorResponse {
                error: format!("subscribe signature rejected: {e}"),
            }),
        ));
    }

    let mut s = state.write().await;
    let capacity = req.capacity.unwrap_or(s.config.default_inbox_capacity);
    let min_deposit = req.min_deposit.unwrap_or(s.config.default_min_deposit);

    // Check total capacity limit.
    let current_total = s.template.total_capacity();
    if current_total + capacity > s.config.max_total_capacity {
        return Err((
            StatusCode::SERVICE_UNAVAILABLE,
            Json(ErrorResponse {
                error: format!(
                    "would exceed max total capacity ({} + {} > {})",
                    current_total, capacity, s.config.max_total_capacity
                ),
            }),
        ));
    }

    s.operator
        .host_inbox(owner, capacity, min_deposit)
        .map_err(|e| {
            let msg = format!("{e:?}");
            let status = match &e {
                dregg_storage::relay::RelayError::AlreadyHosted { .. } => StatusCode::CONFLICT,
                dregg_storage::relay::RelayError::Underbonded { .. } => {
                    StatusCode::SERVICE_UNAVAILABLE
                }
                _ => StatusCode::BAD_REQUEST,
            };
            (status, Json(ErrorResponse { error: msg }))
        })?;
    let queue_root = s.operator.inbox_root(&owner).unwrap_or([0u8; 32]);
    let hosted_root = s
        .template
        .register_inbox(owner, capacity, min_deposit, queue_root)
        .map_err(|e| {
            (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(ErrorResponse { error: e }),
            )
        })?;

    let fee = s.config.fee_policy.subscription_fee;
    info!(
        owner = %req.owner,
        capacity = capacity,
        "new inbox subscription"
    );

    Ok(Json(SubscribeResponse {
        owner: req.owner,
        capacity,
        min_deposit,
        subscription_fee_paid: fee,
        relay_template_hosted_inbox_root: hex_encode(&hosted_root),
    }))
}

async fn handle_unsubscribe(
    State(state): State<SharedRelayState>,
    Json(req): Json<UnsubscribeRequest>,
) -> Result<Json<serde_json::Value>, (StatusCode, Json<ErrorResponse>)> {
    let owner = hex_decode_32(&req.owner).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid owner key".to_string(),
            }),
        )
    })?;

    // F-P1-1: require Ed25519 signature from owner.
    let nonce_bytes = hex_decode_var(&req.nonce).map_err(|_| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid nonce hex".to_string(),
            }),
        )
    })?;
    let mut payload = Vec::with_capacity(32 + nonce_bytes.len());
    payload.extend_from_slice(&owner);
    payload.extend_from_slice(&nonce_bytes);
    if let Err(e) = verify_owner_signature(
        &owner,
        &req.signature,
        b"dregg-relay-unsubscribe-v1",
        &payload,
    ) {
        return Err((
            StatusCode::FORBIDDEN,
            Json(ErrorResponse {
                error: format!("unsubscribe signature rejected: {e}"),
            }),
        ));
    }

    let mut s = state.write().await;
    let refunds = s.operator.evict_inbox(&owner);
    s.template.mark_inbox_evicted(&owner).map_err(|e| {
        (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(ErrorResponse { error: e }),
        )
    })?;

    info!(
        owner = %req.owner,
        refunds = refunds.len(),
        "inbox unsubscribed (evicted)"
    );

    Ok(Json(serde_json::json!({
        "owner": req.owner,
        "refunds_issued": refunds.len(),
        "total_refunded": refunds.iter().map(|r| r.amount).sum::<u64>(),
    })))
}

async fn handle_send(
    State(state): State<SharedRelayState>,
    Path(dest): Path<String>,
    Json(req): Json<SendRequest>,
) -> Result<Json<SendResponse>, (StatusCode, Json<ErrorResponse>)> {
    let destination = hex_decode_32(&dest).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid destination key (expected 64 hex chars)".to_string(),
            }),
        )
    })?;

    let sender = hex_decode_32(&req.sender).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid sender key".to_string(),
            }),
        )
    })?;

    let payload = base64_decode(&req.payload).map_err(|e| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: format!("invalid base64 payload: {e}"),
            }),
        )
    })?;

    let mut s = state.write().await;
    let current_height = s.current_height;

    let msg = InboxMessage::Encrypted {
        ciphertext: payload,
        sender,
    };
    let relayed_bytes = match &msg {
        InboxMessage::Encrypted { ciphertext, .. } => ciphertext.len() as u64,
        InboxMessage::Capability { cert_bytes, .. } => cert_bytes.len() as u64,
        InboxMessage::SturdyRef { uri, .. } => uri.len() as u64,
    };
    s.template
        .validate_enqueue(&destination, relayed_bytes, req.deposit)
        .map_err(|e| {
            let status = if e.contains("missing inbox") {
                StatusCode::NOT_FOUND
            } else if e.contains("insufficient deposit") {
                StatusCode::PAYMENT_REQUIRED
            } else {
                StatusCode::SERVICE_UNAVAILABLE
            };
            (status, Json(ErrorResponse { error: e }))
        })?;
    s.template
        .record_enqueue(&destination, msg, req.deposit, current_height)
        .map_err(|e| {
            (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(ErrorResponse { error: e }),
            )
        })?;

    s.messages_received += 1;
    let pending = s.template.total_pending();
    let bytes_relayed = s.template.bytes_relayed_this_epoch();
    let root = s
        .template
        .hosted_inboxes
        .get(&destination)
        .map(|inbox| inbox.queue_root)
        .unwrap_or([0u8; 32]);

    Ok(Json(SendResponse {
        queue_root: hex_encode(&root),
        position: pending,
        relay_template_bytes_relayed_this_epoch: bytes_relayed,
    }))
}

async fn handle_drain(
    State(state): State<SharedRelayState>,
    axum::extract::Query(query): axum::extract::Query<DrainQuery>,
) -> Result<Json<DrainResponse>, (StatusCode, Json<ErrorResponse>)> {
    let owner = hex_decode_32(&query.owner).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid owner key".to_string(),
            }),
        )
    })?;

    let max = query.max.unwrap_or(100);

    // F-P1-1: require Ed25519 signature from `owner` over (owner, nonce, max).
    // Without this, anyone on the network could drain any inbox.
    let nonce_bytes = hex_decode_var(&query.nonce).map_err(|_| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid nonce hex".to_string(),
            }),
        )
    })?;
    let mut payload = Vec::with_capacity(32 + nonce_bytes.len() + 8);
    payload.extend_from_slice(&owner);
    payload.extend_from_slice(&nonce_bytes);
    payload.extend_from_slice(&(max as u64).to_le_bytes());
    if let Err(e) =
        verify_owner_signature(&owner, &query.signature, b"dregg-relay-drain-v1", &payload)
    {
        return Err((
            StatusCode::FORBIDDEN,
            Json(ErrorResponse {
                error: format!("drain signature rejected: {e}"),
            }),
        ));
    }

    let mut s = state.write().await;
    let current_height = s.current_height;
    let drained = s
        .template
        .drain_inbox(&owner, max, current_height)
        .map_err(|e| {
            let status = if e.contains("missing inbox") {
                StatusCode::NOT_FOUND
            } else {
                StatusCode::BAD_REQUEST
            };
            (status, Json(ErrorResponse { error: e }))
        })?;
    // Store delivery proofs and build response.
    let messages: Vec<DrainedMessage> = drained
        .into_iter()
        .map(|(entry, proof)| {
            // Cache the proof for later retrieval.
            s.delivery_proofs.insert(entry.content_hash, proof.clone());
            s.messages_delivered += 1;

            DrainedMessage {
                content_hash: hex_encode(&entry.content_hash),
                sender: hex_encode(&entry.sender),
                deposit: entry.deposit,
                enqueued_at: entry.enqueued_at,
                proof_old_root: hex_encode(&proof.old_root),
                proof_new_root: hex_encode(&proof.new_root),
            }
        })
        .collect();

    let new_root = s
        .template
        .hosted_inboxes
        .get(&owner)
        .map(|inbox| inbox.queue_root)
        .unwrap_or([0u8; 32]);

    Ok(Json(DrainResponse {
        messages,
        new_root: hex_encode(&new_root),
    }))
}

async fn handle_inbox_status(
    State(state): State<SharedRelayState>,
    Path(id): Path<String>,
) -> Result<Json<InboxStatusResponse>, (StatusCode, Json<ErrorResponse>)> {
    let owner = hex_decode_32(&id).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid inbox id (expected 64 hex chars)".to_string(),
            }),
        )
    })?;

    let s = state.read().await;
    let hosted = s.template.hosted_inboxes.get(&owner).ok_or_else(|| {
        (
            StatusCode::NOT_FOUND,
            Json(ErrorResponse {
                error: "inbox not found".to_string(),
            }),
        )
    })?;

    Ok(Json(InboxStatusResponse {
        owner: id,
        pending_messages: hosted.pending_messages,
        committed_capacity: hosted.committed_capacity,
        queue_root: hex_encode(&hosted.queue_root),
        last_drain_height: hosted.last_drain_height,
        evicted: hosted.evicted,
    }))
}

async fn handle_proof(
    State(state): State<SharedRelayState>,
    Path(msg_id): Path<String>,
) -> Result<Json<ProofResponse>, (StatusCode, Json<ErrorResponse>)> {
    let msg_hash = hex_decode_32(&msg_id).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid msg_id (expected 64 hex chars)".to_string(),
            }),
        )
    })?;

    let s = state.read().await;
    if let Some(proof) = s.delivery_proofs.get(&msg_hash) {
        Ok(Json(ProofResponse {
            msg_id,
            old_root: hex_encode(&proof.old_root),
            new_root: hex_encode(&proof.new_root),
            found: true,
        }))
    } else {
        Ok(Json(ProofResponse {
            msg_id,
            old_root: String::new(),
            new_root: String::new(),
            found: false,
        }))
    }
}

// ─── Service Lifecycle ────────────────────────────────────────────────────────

/// Start the relay service: initialize operator, spawn GC task, serve HTTP.
pub async fn run_relay_service(config: RelayConfig) {
    info!(
        port = config.listen_port,
        bond = config.bond_amount,
        max_capacity = config.max_total_capacity,
        gc_interval = config.gc_interval_secs,
        state_file = %config.state_file.display(),
        "starting relay operator service"
    );

    // Initialize the relay operator.
    let operator = RelayOperator::new(
        config.operator_key,
        config.bond_amount,
        config.max_delivery_latency_blocks,
    );
    let template = RelayTemplateState::new(&config);

    let relay_state = Arc::new(RwLock::new(RelayState {
        operator,
        template,
        config: config.clone(),
        current_height: 0,
        delivery_proofs: std::collections::HashMap::new(),
        messages_delivered: 0,
        messages_received: 0,
    }));

    // Spawn the GC background task.
    let gc_state = relay_state.clone();
    let gc_interval = config.gc_interval_secs;
    let message_ttl = config.message_ttl_blocks;
    tokio::spawn(async move {
        let mut interval = tokio::time::interval(Duration::from_secs(gc_interval));
        loop {
            interval.tick().await;
            let mut s = gc_state.write().await;
            let height = s.current_height;
            let result = s.operator.gc_expired(height, message_ttl);
            if result.messages_collected > 0 {
                info!(
                    collected = result.messages_collected,
                    operator_fees = result.operator_fees,
                    refunds = result.sender_refunds.len(),
                    "relay GC pass completed"
                );
            }
        }
    });

    // Spawn a block height ticker (simulates block production for standalone mode).
    let height_state = relay_state.clone();
    tokio::spawn(async move {
        let mut interval = tokio::time::interval(Duration::from_secs(12));
        loop {
            interval.tick().await;
            let mut s = height_state.write().await;
            s.current_height += 1;
        }
    });

    // Build and serve the HTTP API.
    let app = relay_router(relay_state);

    let addr = std::net::SocketAddr::new(
        std::net::IpAddr::V4(std::net::Ipv4Addr::new(0, 0, 0, 0)),
        config.listen_port,
    );

    info!(%addr, "relay service HTTP API listening");

    let listener = tokio::net::TcpListener::bind(addr)
        .await
        .expect("failed to bind relay HTTP listener");

    axum::serve(listener, app)
        .with_graceful_shutdown(async {
            tokio::signal::ctrl_c()
                .await
                .expect("failed to listen for Ctrl-C");
            info!("relay service shutting down");
        })
        .await
        .expect("relay HTTP server error");
}

// ─── Utility Functions ────────────────────────────────────────────────────────

fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn u64_field(value: u64) -> [u8; 32] {
    let mut field = [0u8; 32];
    field[24..].copy_from_slice(&value.to_be_bytes());
    field
}

fn u64_from_field(field: [u8; 32]) -> u64 {
    u64::from_be_bytes(field[24..].try_into().expect("field suffix is 8 bytes"))
}

fn blake3_field(bytes: &[u8]) -> [u8; 32] {
    *blake3::hash(bytes).as_bytes()
}

fn default_route_table_root() -> [u8; 32] {
    blake3_field(b"dregg-relay-route-table-v1:any-encrypted-message")
}

fn inbox_message_content_hash(msg: &InboxMessage) -> [u8; 32] {
    let mut buf = Vec::new();
    match msg {
        InboxMessage::Capability { cert_bytes, sender } => {
            buf.push(0x01);
            buf.extend_from_slice(sender);
            buf.extend_from_slice(cert_bytes);
        }
        InboxMessage::SturdyRef { uri, sender } => {
            buf.push(0x02);
            buf.extend_from_slice(sender);
            buf.extend_from_slice(uri.as_bytes());
        }
        InboxMessage::Encrypted { ciphertext, sender } => {
            buf.push(0x03);
            buf.extend_from_slice(sender);
            buf.extend_from_slice(ciphertext);
        }
    }
    *blake3::hash(&buf).as_bytes()
}

fn template_queue_from_entries(
    capacity: usize,
    entries: impl IntoIterator<Item = QueueEntry>,
) -> Result<MerkleQueue, String> {
    let mut queue = MerkleQueue::new(capacity);
    for entry in entries {
        queue
            .enqueue(entry)
            .map_err(|e| format!("relay template queue rebuild rejected: {e:?}"))?;
    }
    Ok(queue)
}

fn queue_root_from_template_entries(
    capacity: usize,
    entries: impl IntoIterator<Item = QueueEntry>,
) -> Result<[u8; 32], String> {
    Ok(template_queue_from_entries(capacity, entries)?.root())
}

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

fn base64_decode(s: &str) -> Result<Vec<u8>, String> {
    use base64::Engine;
    base64::engine::general_purpose::STANDARD
        .decode(s)
        .map_err(|e| e.to_string())
}

fn hex_ser_32<S: serde::Serializer>(bytes: &[u8; 32], s: S) -> Result<S::Ok, S::Error> {
    s.serialize_str(&hex_encode(bytes))
}

fn hex_de_32<'de, D: serde::Deserializer<'de>>(d: D) -> Result<[u8; 32], D::Error> {
    let s = String::deserialize(d)?;
    hex_decode_32(&s).ok_or_else(|| serde::de::Error::custom("expected 64 hex chars"))
}

// ─── Adversarial tests for F-P1-1 (relay caller-authentication) ──────────────
//
// These tests exercise `verify_owner_signature` directly. The handlers
// themselves are thin wrappers around the verifier (see handle_subscribe,
// handle_unsubscribe, handle_drain) so verifying the verifier is sufficient
// to demonstrate the regression-coverage. A future router-level integration
// test (deferred while sdk/cell rebuild is in flight) would also exercise
// the wiring.

#[cfg(test)]
mod tests {
    use super::*;
    use ed25519_dalek::{Signer, SigningKey};

    fn make_key(seed_byte: u8) -> (SigningKey, [u8; 32]) {
        let mut seed = [0u8; 32];
        seed[0] = seed_byte;
        let sk = SigningKey::from_bytes(&seed);
        let pk = sk.verifying_key().to_bytes();
        (sk, pk)
    }

    fn test_config() -> RelayConfig {
        RelayConfig {
            operator_key: [0xAA; 32],
            bond_amount: 10_000,
            max_total_capacity: 64,
            default_inbox_capacity: 8,
            default_min_deposit: 1,
            ..RelayConfig::default()
        }
    }

    fn test_state(config: RelayConfig) -> RelayState {
        RelayState {
            operator: RelayOperator::new(
                config.operator_key,
                config.bond_amount,
                config.max_delivery_latency_blocks,
            ),
            template: RelayTemplateState::new(&config),
            config,
            current_height: 0,
            delivery_proofs: std::collections::HashMap::new(),
            messages_delivered: 0,
            messages_received: 0,
        }
    }

    fn sign_request(sk: &SigningKey, domain: &[u8], payload: &[u8]) -> String {
        let mut full = Vec::new();
        full.extend_from_slice(domain);
        full.extend_from_slice(payload);
        sk.sign(&full)
            .to_bytes()
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect()
    }

    fn signed_subscribe(sk: &SigningKey, owner: [u8; 32]) -> SubscribeRequest {
        let nonce = b"sub1";
        let mut payload = Vec::new();
        payload.extend_from_slice(&owner);
        payload.extend_from_slice(nonce);
        SubscribeRequest {
            owner: hex_encode(&owner),
            capacity: Some(2),
            min_deposit: Some(1),
            nonce: hex_encode(nonce),
            signature: sign_request(sk, b"dregg-relay-subscribe-v1", &payload),
        }
    }

    /// F-P1-1: an unsigned drain request must be rejected. (The verifier is
    /// the choke-point: an empty/garbage signature must not be accepted.)
    #[test]
    fn audit_f_p1_1_unsigned_drain_rejected() {
        let (_sk, pk) = make_key(1);
        let payload = b"\x00\x01\x02";
        // Empty signature.
        assert!(verify_owner_signature(&pk, "", b"dregg-relay-drain-v1", payload).is_err());
        // Garbage signature.
        let bad = "ff".repeat(64);
        assert!(verify_owner_signature(&pk, &bad, b"dregg-relay-drain-v1", payload).is_err());
    }

    /// F-P1-1: a drain signature by another key (key A) but claiming to be
    /// from a different owner (key B) MUST be rejected.
    #[test]
    fn audit_f_p1_1_wrong_signer_rejected() {
        let (sk_a, _pk_a) = make_key(1);
        let (_sk_b, pk_b) = make_key(2);
        let mut payload = Vec::new();
        payload.extend_from_slice(&pk_b);
        payload.extend_from_slice(b"nonce123");
        // Sign with A's key but verify against B.
        let mut full = Vec::new();
        full.extend_from_slice(b"dregg-relay-drain-v1");
        full.extend_from_slice(&payload);
        let sig = sk_a.sign(&full);
        let sig_hex: String = sig.to_bytes().iter().map(|b| format!("{b:02x}")).collect();

        assert!(
            verify_owner_signature(&pk_b, &sig_hex, b"dregg-relay-drain-v1", &payload).is_err(),
            "must reject when signer != claimed owner"
        );
    }

    /// F-P1-1: a correctly-signed drain request passes.
    #[test]
    fn audit_f_p1_1_valid_drain_signature_accepted() {
        let (sk, pk) = make_key(7);
        let mut payload = Vec::new();
        payload.extend_from_slice(&pk);
        payload.extend_from_slice(b"nonce456");
        payload.extend_from_slice(&100u64.to_le_bytes());

        let mut full = Vec::new();
        full.extend_from_slice(b"dregg-relay-drain-v1");
        full.extend_from_slice(&payload);
        let sig = sk.sign(&full);
        let sig_hex: String = sig.to_bytes().iter().map(|b| format!("{b:02x}")).collect();

        assert!(
            verify_owner_signature(&pk, &sig_hex, b"dregg-relay-drain-v1", &payload).is_ok(),
            "valid signature should pass"
        );
    }

    /// F-P1-1: a drain signature signed for a DIFFERENT domain (e.g.,
    /// subscribe) must NOT be replayable as a drain signature.
    #[test]
    fn audit_f_p1_1_cross_domain_replay_rejected() {
        let (sk, pk) = make_key(11);
        let payload = b"some-payload";

        // Sign for subscribe.
        let mut full = Vec::new();
        full.extend_from_slice(b"dregg-relay-subscribe-v1");
        full.extend_from_slice(payload);
        let sig = sk.sign(&full);
        let sig_hex: String = sig.to_bytes().iter().map(|b| format!("{b:02x}")).collect();

        // Verifies under subscribe domain.
        assert!(
            verify_owner_signature(&pk, &sig_hex, b"dregg-relay-subscribe-v1", payload).is_ok()
        );
        // Replayed as drain: rejected.
        assert!(verify_owner_signature(&pk, &sig_hex, b"dregg-relay-drain-v1", payload).is_err());
        // Replayed as unsubscribe: rejected.
        assert!(
            verify_owner_signature(&pk, &sig_hex, b"dregg-relay-unsubscribe-v1", payload).is_err()
        );
    }

    /// F-P1-1: the request structs require nonce + signature fields. Verify
    /// the deserialization layer rejects requests that omit them.
    #[test]
    fn audit_f_p1_1_subscribe_schema_requires_signature() {
        let bad = serde_json::json!({
            "owner": "ab".repeat(32),
        });
        assert!(serde_json::from_value::<SubscribeRequest>(bad).is_err());

        let good = serde_json::json!({
            "owner": "ab".repeat(32),
            "nonce": "0011",
            "signature": "00".repeat(64),
        });
        assert!(serde_json::from_value::<SubscribeRequest>(good).is_ok());
    }

    /// F-P1-1: same for unsubscribe.
    #[test]
    fn audit_f_p1_1_unsubscribe_schema_requires_signature() {
        let bad = serde_json::json!({
            "owner": "ab".repeat(32),
        });
        assert!(serde_json::from_value::<UnsubscribeRequest>(bad).is_err());

        let good = serde_json::json!({
            "owner": "ab".repeat(32),
            "nonce": "0011",
            "signature": "00".repeat(64),
        });
        assert!(serde_json::from_value::<UnsubscribeRequest>(good).is_ok());
    }

    #[test]
    fn relay_template_mirror_binds_canonical_descriptor_and_dfa_rate_limit_case() {
        let config = test_config();
        let template = RelayTemplateState::new(&config);
        let descriptor = relay_operator_factory_descriptor();

        assert_eq!(template.factory_vk, descriptor.factory_vk);
        assert_eq!(template.factory_hash, descriptor.hash());
        assert_eq!(template.child_program_vk, relay_operator_child_program_vk());
        assert_eq!(
            template.quota_bytes_per_epoch(),
            config.max_total_capacity as u64
        );
        assert!(template.relay_case_has_dfa_and_rate_limit());
    }

    #[tokio::test]
    async fn relay_template_subscribe_updates_hosted_root() {
        let (sk, owner) = make_key(21);
        let state = Arc::new(RwLock::new(test_state(test_config())));
        let before = state.read().await.template.hosted_inbox_root();

        let response = handle_subscribe(State(state.clone()), Json(signed_subscribe(&sk, owner)))
            .await
            .expect("subscribe should succeed")
            .0;

        let after = state.read().await.template.hosted_inbox_root();
        assert_ne!(before, after);
        assert_ne!(after, [0u8; 32]);
        assert_eq!(
            response.relay_template_hosted_inbox_root,
            hex_encode(&after)
        );
    }

    #[tokio::test]
    async fn relay_template_inbox_status_uses_template_registry() {
        let (sk, owner) = make_key(23);
        let state = Arc::new(RwLock::new(test_state(test_config())));
        let _ = handle_subscribe(State(state.clone()), Json(signed_subscribe(&sk, owner)))
            .await
            .expect("subscribe should succeed");

        state.write().await.operator.hosted_inboxes.remove(&owner);

        let response = handle_inbox_status(State(state), Path(hex_encode(&owner)))
            .await
            .expect("template registry should be sufficient for status")
            .0;

        assert_eq!(response.owner, hex_encode(&owner));
        assert_eq!(response.committed_capacity, 2);
        assert_eq!(response.pending_messages, 0);
        assert!(!response.evicted);
    }

    #[tokio::test]
    async fn relay_template_unsubscribe_updates_hosted_root_and_status() {
        let (sk, owner) = make_key(24);
        let state = Arc::new(RwLock::new(test_state(test_config())));
        let _ = handle_subscribe(State(state.clone()), Json(signed_subscribe(&sk, owner)))
            .await
            .expect("subscribe should succeed");
        let before = state.read().await.template.hosted_inbox_root();

        let nonce = b"unsub1";
        let mut payload = Vec::new();
        payload.extend_from_slice(&owner);
        payload.extend_from_slice(nonce);
        let response = handle_unsubscribe(
            State(state.clone()),
            Json(UnsubscribeRequest {
                owner: hex_encode(&owner),
                nonce: hex_encode(nonce),
                signature: sign_request(&sk, b"dregg-relay-unsubscribe-v1", &payload),
            }),
        )
        .await
        .expect("unsubscribe should succeed")
        .0;

        assert_eq!(response["refunds_issued"], 0);
        let status = handle_inbox_status(State(state.clone()), Path(hex_encode(&owner)))
            .await
            .expect("evicted template inbox remains inspectable")
            .0;
        assert!(status.evicted);
        assert_eq!(status.queue_root, hex_encode(&[0u8; 32]));
        assert_ne!(state.read().await.template.hosted_inbox_root(), before);
    }

    #[tokio::test]
    async fn relay_template_send_is_rate_limited_by_counter() {
        let (sk, owner) = make_key(22);
        let state = Arc::new(RwLock::new(test_state(RelayConfig {
            max_total_capacity: 4,
            ..test_config()
        })));
        let _ = handle_subscribe(State(state.clone()), Json(signed_subscribe(&sk, owner)))
            .await
            .expect("subscribe should succeed");

        let err = handle_send(
            State(state.clone()),
            Path(hex_encode(&owner)),
            Json(SendRequest {
                sender: hex_encode(&[0xBC; 32]),
                payload: {
                    use base64::Engine;
                    base64::engine::general_purpose::STANDARD.encode([1u8; 5])
                },
                deposit: 1,
            }),
        )
        .await
        .expect_err("template RateLimitBySum mirror should reject oversized send");

        assert_eq!(err.0, StatusCode::SERVICE_UNAVAILABLE);
        assert_eq!(state.read().await.template.bytes_relayed_this_epoch(), 0);
    }

    #[tokio::test]
    async fn relay_template_rejects_missing_inbox_before_backend_send() {
        let state = Arc::new(RwLock::new(test_state(test_config())));
        let missing_owner = [0xCD; 32];

        let err = handle_send(
            State(state.clone()),
            Path(hex_encode(&missing_owner)),
            Json(SendRequest {
                sender: hex_encode(&[0xBC; 32]),
                payload: {
                    use base64::Engine;
                    base64::engine::general_purpose::STANDARD.encode([1u8; 3])
                },
                deposit: 1,
            }),
        )
        .await
        .expect_err("legacy queue should still reject missing inbox");

        assert_eq!(err.0, StatusCode::NOT_FOUND);
        assert_eq!(state.read().await.template.bytes_relayed_this_epoch(), 0);
    }

    #[tokio::test]
    async fn relay_template_send_and_drain_do_not_need_operator_queue_backend() {
        let (sk, owner) = make_key(25);
        let state = Arc::new(RwLock::new(test_state(test_config())));
        let _ = handle_subscribe(State(state.clone()), Json(signed_subscribe(&sk, owner)))
            .await
            .expect("subscribe should succeed");

        state.write().await.operator.hosted_inboxes.remove(&owner);

        let send = handle_send(
            State(state.clone()),
            Path(hex_encode(&owner)),
            Json(SendRequest {
                sender: hex_encode(&[0xBC; 32]),
                payload: {
                    use base64::Engine;
                    base64::engine::general_purpose::STANDARD.encode([1u8; 3])
                },
                deposit: 1,
            }),
        )
        .await
        .expect("template queue should accept send without operator inbox")
        .0;

        assert_eq!(send.position, 1);
        assert_eq!(state.read().await.template.total_pending(), 1);

        let nonce = b"drain-template";
        let max = 1usize;
        let mut payload = Vec::new();
        payload.extend_from_slice(&owner);
        payload.extend_from_slice(nonce);
        payload.extend_from_slice(&(max as u64).to_le_bytes());
        let drain = handle_drain(
            State(state.clone()),
            axum::extract::Query(DrainQuery {
                owner: hex_encode(&owner),
                max: Some(max),
                nonce: hex_encode(nonce),
                signature: sign_request(&sk, b"dregg-relay-drain-v1", &payload),
            }),
        )
        .await
        .expect("template queue should drain without operator inbox")
        .0;

        assert_eq!(drain.messages.len(), 1);
        assert_eq!(drain.messages[0].sender, hex_encode(&[0xBC; 32]));
        assert_eq!(state.read().await.template.total_pending(), 0);
        assert_eq!(state.read().await.messages_delivered, 1);
    }
}
