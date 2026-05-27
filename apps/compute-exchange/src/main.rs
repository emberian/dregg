//! Compute Exchange — a privacy-preserving marketplace for agent compute services.
//!
//! Providers offer GPU compute with SLA guarantees, proving capacity via ZK proofs.
//! Consumers place orders with sealed-bid auctions (commit-reveal anti-frontrunning).
//! Settlement uses atomic escrow: payment locked until proof of delivery, SLA bond
//! forfeited on violation.
//!
//! # Architecture
//!
//! ```text
//! ┌──────────────┐     ┌──────────────────┐     ┌──────────────┐
//! │   Provider   │────>│ Compute Exchange  │<────│   Consumer   │
//! │  (GPU farm)  │     │    (this app)     │     │   (agent)    │
//! └──────────────┘     └──────────────────┘     └──────────────┘
//!        │                      │                       │
//!   List offering         Match + Settle          Place order
//!   (qualification)      (escrow + partial)     (commit-reveal)
//! ```

// REVIEW[P2]: The brief for this app described "new-world framework primitives"
// (nameservice auto-registration, per-provider `/providers/{id}/publish-name`,
// a `BatchExecutor`-based `/executor/jobs` + `/executor/run`, and `src/executor.rs`).
// None of these are present in the current tree — there is no `executor` module,
// no `discovery::NameserviceClient` use, no `AppServer::with_name`, and the
// router below has no `/providers/.../publish-name` or `/executor/*` routes.
// Compute-exchange has NOT been upgraded to the new primitives; only the legacy
// orderbook / commit-reveal / optimistic-settlement code is present. The
// nameservice/executor work must still be done, OR the brief is stale.

mod auction;
mod delivery_verification;
mod orderbook;
mod persistence;
mod qualification;
mod settlement;
mod state;

use std::net::SocketAddr;

use axum::{
    Json, Router,
    extract::{Path, State},
    http::{HeaderMap, StatusCode},
    response::IntoResponse,
    routing::{get, post},
};
use clap::Parser;
use serde::{Deserialize, Serialize};
use serde_json::json;
use tracing::{error, info, warn};

use dregg_app_framework::dispute::{
    self as dispute_framework, ComputeMetrics, DeliveryClaim, DisputeConfig, DisputeEvidence,
    OptimisticSettlement, SettlementState as OptimisticState,
};
use dregg_app_framework::hex::{bytes32_to_hex, hex_to_bytes32};
use dregg_app_framework::{CellId, FillConstraints};

use crate::auction::compute_order_commitment;
use crate::orderbook::{
    GpuType, Offering, Order, OrderStatus, SlaGuarantees, compute_offering_id, compute_order_id,
    find_matching_offering,
};
use crate::qualification::{ComputeQualification, verify_compute_qualification};
use crate::settlement::{
    DEFAULT_TIMEOUT_BLOCKS, Dispute, DisputeStatus, SLA_BOND_PERCENTAGE, Settlement,
    SettlementStatus, compute_settlement_id, create_settlement_escrows,
};
use crate::state::AppState;

// =============================================================================
// Request / Response types
// =============================================================================

#[derive(Debug, Serialize, Deserialize)]
struct CreateOfferingRequest {
    /// Provider cell ID (hex-encoded, 64 chars).
    provider_cell: String,
    /// GPU type string.
    gpu_type: String,
    /// Number of GPUs.
    gpu_count: u32,
    /// Hourly rate in smallest denomination.
    hourly_rate: u64,
    /// Available hours.
    available_hours: u64,
    /// SLA uptime in basis points (e.g., 999 = 99.9%).
    sla_uptime_bps: u32,
    /// SLA max latency in ms.
    sla_max_latency_ms: u32,
    /// Whether preemption recovery is supported.
    sla_preemption_recovery: bool,
    /// Optional qualification proof bytes (hex-encoded).
    qualification_proof: Option<String>,
}

#[derive(Debug, Serialize, Deserialize)]
struct CreateOrderRequest {
    /// Consumer cell ID (hex-encoded).
    consumer_cell: String,
    /// Required GPU type.
    gpu_type: String,
    /// Minimum GPUs needed.
    min_gpu_count: u32,
    /// Maximum hourly rate willing to pay.
    max_hourly_rate: u64,
    /// Duration needed in hours.
    duration_hours: u64,
    /// Minimum fill amount (compute-hours).
    min_fill_hours: u64,
    /// Maximum fill amount (compute-hours).
    max_fill_hours: u64,
    /// Fill-or-kill: must fill entirely or not at all.
    fill_or_kill: bool,
    /// Secret for the commit-reveal protocol.
    commit_secret: String,
}

#[derive(Debug, Serialize, Deserialize)]
struct RevealOrderRequest {
    /// The secret used during commit phase (hex-encoded, 64 chars).
    secret: String,
}

#[derive(Debug, Serialize, Deserialize)]
struct CompleteSettlementRequest {
    /// Provider cell ID (hex-encoded).
    provider_cell: String,
    /// Delivery proof bytes (hex-encoded).
    delivery_proof: String,
}

/// Request body for the optimistic claim submission.
/// The provider attests to delivery metrics; the STARK proof is OPTIONAL EVIDENCE.
#[derive(Debug, Serialize, Deserialize)]
struct SubmitClaimRequest {
    /// Provider cell ID (hex-encoded).
    provider_cell: String,
    /// FLOPS delivered.
    flops_delivered: u64,
    /// Duration of the computation in seconds.
    duration_seconds: u64,
    /// Quality score (0-10000 basis points).
    quality_bps: u32,
    /// Output hash (hex-encoded, 64 chars) — commitment to the result.
    output_hash: String,
    /// Optional: input hash for re-execution verification.
    input_hash: Option<String>,
    /// Provider's Ed25519 signature over the metrics (hex-encoded).
    signature: String,
    /// Optional STARK proof as evidence (hex-encoded). Strengthens the claim but
    /// is NOT required for payment. The dispute window is the enforcement mechanism.
    delivery_proof: Option<String>,
}

/// Request body for challenging a claim during the dispute window.
#[derive(Debug, Serialize, Deserialize)]
struct ChallengeClaimRequest {
    /// Challenger cell ID (hex-encoded).
    challenger_cell: String,
    /// Amount the challenger is staking (must meet minimum).
    challenger_stake: u64,
    /// Type of challenge evidence.
    evidence_type: String,
    /// Evidence payload (interpretation depends on evidence_type):
    /// - "re_execution_mismatch": JSON with claimed_output_hash, actual_output_hash, optional proof
    /// - "proof_invalid": JSON with verification_error
    /// - "metrics_impossible": JSON with reason, max_possible_flops
    /// - "uptime_violation": JSON with missed_blocks, required_uptime_bps, actual_uptime_bps
    evidence_payload: serde_json::Value,
}

/// Request body for finalizing an unchallenged settlement.
#[derive(Debug, Serialize, Deserialize)]
struct FinalizeSettlementRequest {
    /// Who is requesting finalization (provider or anyone after window closes).
    requestor_cell: String,
}

#[derive(Debug, Serialize, Deserialize)]
struct CreateDisputeRequest {
    /// Initiator cell ID (hex-encoded).
    initiator_cell: String,
    /// Reason for the dispute.
    reason: String,
}

// =============================================================================
// CLI Arguments
// =============================================================================

/// Compute Exchange — a privacy-preserving marketplace for agent compute services.
#[derive(Parser, Debug)]
#[command(name = "compute-exchange")]
struct Args {
    /// Federation root hash (64 hex chars). If not provided, fetches from the node.
    #[arg(long, env = "DREGG_FEDERATION_ROOT")]
    federation_root: Option<String>,

    /// URL of a running dregg-node to fetch the federation root from.
    /// The app will query /status and /federation/roots on startup.
    #[arg(long, default_value = "http://127.0.0.1:8420", env = "DREGG_NODE_URL")]
    node_url: String,

    /// Listen address.
    #[arg(long, default_value = "127.0.0.1:3040", env = "DREGG_LISTEN")]
    listen: SocketAddr,

    /// Directory for persisting state across restarts. If not set, state is ephemeral.
    #[arg(long, env = "DREGG_STATE_DIR")]
    state_dir: Option<std::path::PathBuf>,
}

// =============================================================================
// Main
// =============================================================================

/// Parse a 64-char hex string into a [u8; 32] federation root.
fn parse_federation_root(hex: &str) -> Result<[u8; 32], String> {
    let hex = hex.strip_prefix("0x").unwrap_or(hex);
    hex_to_bytes32(hex).map_err(|e| format!("invalid federation root hex: {e}"))
}

// =============================================================================
// Node Client
// =============================================================================

/// Response shape from the node's GET /status endpoint.
#[derive(Deserialize)]
struct NodeStatusResponse {
    healthy: bool,
    latest_height: u64,
    #[allow(dead_code)]
    peer_count: usize,
}

/// Response shape from the node's GET /federation/roots endpoint.
#[derive(Deserialize)]
struct AttestedRootInfo {
    #[allow(dead_code)]
    height: u64,
    merkle_root: String,
    #[allow(dead_code)]
    timestamp: i64,
    #[allow(dead_code)]
    signatures: usize,
}

/// Fetch the latest federation root from a running node.
///
/// Queries `/federation/roots` and returns the merkle_root of the highest-height
/// attested root. Falls back to `/status` to verify the node is reachable.
async fn fetch_federation_root(node_url: &str) -> Result<[u8; 32], String> {
    let client = reqwest::Client::builder()
        .timeout(std::time::Duration::from_secs(5))
        .build()
        .map_err(|e| format!("failed to build HTTP client: {e}"))?;

    // First verify the node is healthy.
    let status_url = format!("{node_url}/status");
    let status: NodeStatusResponse = client
        .get(&status_url)
        .send()
        .await
        .map_err(|e| format!("node unreachable at {status_url}: {e}"))?
        .json()
        .await
        .map_err(|e| format!("invalid status response: {e}"))?;

    if !status.healthy {
        return Err("node reports unhealthy status".to_string());
    }

    // Fetch attested roots.
    let roots_url = format!("{node_url}/federation/roots");
    let roots: Vec<AttestedRootInfo> = client
        .get(&roots_url)
        .send()
        .await
        .map_err(|e| format!("failed to fetch federation roots: {e}"))?
        .json()
        .await
        .map_err(|e| format!("invalid federation roots response: {e}"))?;

    if roots.is_empty() {
        return Err(format!(
            "node at height {} has no attested roots yet",
            status.latest_height
        ));
    }

    // Use the last root (highest height, the list is ordered).
    let latest = roots.last().unwrap();
    let root = hex_to_bytes32(&latest.merkle_root)
        .map_err(|e| format!("invalid merkle_root hex from node: {e}"))?;

    if root == [0u8; 32] {
        return Err("node returned zeroed federation root".to_string());
    }

    Ok(root)
}

#[tokio::main]
async fn main() {
    tracing_subscriber::fmt()
        .with_target(false)
        .with_level(true)
        .init();

    let args = Args::parse();

    // Resolve federation root: explicit > node fetch > refuse to start.
    let federation_root = match &args.federation_root {
        Some(hex) => match parse_federation_root(hex) {
            Ok(root) => {
                info!(
                    root = %bytes32_to_hex(&root),
                    "federation root configured (explicit)"
                );
                root
            }
            Err(e) => {
                error!("{e}");
                std::process::exit(1);
            }
        },
        None => {
            // Fetch from the node (required).
            info!(node_url = %args.node_url, "fetching federation root from node...");
            match fetch_federation_root(&args.node_url).await {
                Ok(root) => {
                    info!(
                        root = %bytes32_to_hex(&root),
                        node_url = %args.node_url,
                        "federation root fetched from node"
                    );
                    root
                }
                Err(e) => {
                    error!(
                        "cannot reach node at {}: {e}\n\
                         A federation root is required for verification. Either:\n\
                         - Start a devnet node (dregg-node) at the default address, or\n\
                         - Pass --node-url pointing to a running node, or\n\
                         - Pass --federation-root explicitly.",
                        args.node_url
                    );
                    std::process::exit(1);
                }
            }
        }
    };

    let state = match &args.state_dir {
        Some(dir) => {
            // Ensure the state directory exists.
            if let Err(e) = std::fs::create_dir_all(dir) {
                error!("failed to create state directory {}: {e}", dir.display());
                std::process::exit(1);
            }
            // Load persisted state if available.
            match persistence::load_state(dir, federation_root) {
                Ok(s) => {
                    info!(state_dir = %dir.display(), "state loaded from disk");
                    s
                }
                Err(e) => {
                    warn!(
                        state_dir = %dir.display(),
                        error = %e,
                        "no persisted state found (starting fresh)"
                    );
                    AppState::new(federation_root, Some(dir.clone()))
                }
            }
        }
        None => AppState::new(federation_root, None),
    };

    let app = Router::new()
        // Offering lifecycle
        .route("/offerings", post(create_offering))
        .route("/offerings", get(list_offerings))
        // Order lifecycle (commit-reveal)
        .route("/orders", post(create_order))
        .route("/orders/{id}/reveal", post(reveal_order))
        .route("/orders/{id}", get(get_order))
        // Settlement (legacy: STARK-enforced)
        .route("/settlements/{id}/complete", post(complete_settlement))
        // Optimistic settlement (new: dispute-window enforced)
        .route("/settlements/{id}/claim", post(submit_claim))
        .route("/settlements/{id}/challenge", post(challenge_claim))
        .route("/settlements/{id}/finalize", post(finalize_settlement))
        // Disputes (legacy)
        .route("/disputes/{id}", post(create_dispute))
        // Utility
        .route("/health", get(health_check))
        .route("/admin/height", post(advance_height))
        .route("/admin/federation-root", post(admin_set_federation_root))
        .with_state(state);

    let addr = args.listen;
    info!("compute exchange listening on {addr}");

    let listener = tokio::net::TcpListener::bind(addr)
        .await
        .expect("failed to bind");

    axum::serve(listener, app).await.expect("server error");
}

// =============================================================================
// Handlers
// =============================================================================

/// POST /offerings — list a compute offering with optional qualification proof.
async fn create_offering(
    State(state): State<AppState>,
    Json(req): Json<CreateOfferingRequest>,
) -> impl IntoResponse {
    let provider = match cell_id_from_hex(&req.provider_cell) {
        Some(id) => id,
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid provider_cell hex"})),
            );
        }
    };

    let gpu_type = parse_gpu_type(&req.gpu_type);
    let federation_root = state.federation_root().await;

    // Verify qualification proof if provided.
    if let Some(ref proof_hex) = req.qualification_proof {
        let proof_bytes = match hex_decode(proof_hex) {
            Some(b) => b,
            None => {
                return (
                    StatusCode::BAD_REQUEST,
                    Json(json!({"error": "invalid qualification_proof hex"})),
                );
            }
        };

        let requirement = ComputeQualification::MinGpuCount {
            gpu_type: req.gpu_type.clone(),
            min_count: req.gpu_count as u64,
        };

        let engine = state.engine_read().await;
        match verify_compute_qualification(&engine, &requirement, &proof_bytes, federation_root) {
            Ok(true) => {}
            Ok(false) => {
                return (
                    StatusCode::FORBIDDEN,
                    Json(json!({"error": "qualification proof does not meet threshold"})),
                );
            }
            Err(e) => {
                warn!(error = %e, "qualification verification failed");
                return (
                    StatusCode::FORBIDDEN,
                    Json(json!({"error": format!("qualification rejected: {e}")})),
                );
            }
        }
    }

    let current_height = state.current_height().await;
    let offering_id = compute_offering_id(&provider, &gpu_type, req.hourly_rate, current_height);

    let qualification_proof_hash = req
        .qualification_proof
        .as_ref()
        .map(|p| *blake3::hash(p.as_bytes()).as_bytes());

    let offering = Offering {
        id: offering_id,
        provider,
        gpu_type,
        gpu_count: req.gpu_count,
        hourly_rate: req.hourly_rate,
        available_hours: req.available_hours,
        sla: SlaGuarantees {
            uptime_bps: req.sla_uptime_bps,
            max_latency_ms: req.sla_max_latency_ms,
            preemption_recovery: req.sla_preemption_recovery,
        },
        available: true,
        created_at: current_height,
        qualification_proof_hash,
    };

    let id_hex = bytes32_to_hex(&offering_id);
    info!(offering_id = %id_hex, gpu_type = %req.gpu_type, rate = req.hourly_rate, "offering created");

    state.insert_offering(offering).await;

    (
        StatusCode::CREATED,
        Json(json!({
            "id": id_hex,
            "status": "active"
        })),
    )
}

/// GET /offerings — browse available compute offerings.
async fn list_offerings(State(state): State<AppState>) -> impl IntoResponse {
    let offerings = state.list_offerings().await;
    let summaries: Vec<serde_json::Value> = offerings
        .iter()
        .map(|o| {
            json!({
                "id": bytes32_to_hex(&o.id),
                "gpu_type": format!("{}", o.gpu_type),
                "gpu_count": o.gpu_count,
                "hourly_rate": o.hourly_rate,
                "available_hours": o.available_hours,
                "sla_uptime_bps": o.sla.uptime_bps,
                "qualified": o.qualification_proof_hash.is_some(),
            })
        })
        .collect();

    Json(json!({
        "offerings": summaries,
        "count": summaries.len()
    }))
}

/// POST /orders — place an order (commit phase of sealed-bid auction).
///
/// The order details are committed but not revealed. Other participants see
/// "someone committed to buying compute" but not the details.
async fn create_order(
    State(state): State<AppState>,
    Json(req): Json<CreateOrderRequest>,
) -> impl IntoResponse {
    let consumer = match cell_id_from_hex(&req.consumer_cell) {
        Some(id) => id,
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid consumer_cell hex"})),
            );
        }
    };

    let secret = match hex_to_bytes32(&req.commit_secret) {
        Ok(s) => s,
        Err(_) => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "commit_secret must be 64 hex chars (32 bytes)"})),
            );
        }
    };

    let gpu_type = parse_gpu_type(&req.gpu_type);
    let current_height = state.current_height().await;
    let order_id = compute_order_id(&consumer, &gpu_type, req.max_hourly_rate, current_height);

    let fill_constraints = FillConstraints {
        min_fill_amount: req.min_fill_hours,
        max_fill_amount: req.max_fill_hours,
        fill_or_kill: req.fill_or_kill,
        remaining_after_fill: None,
        generation: 0,
    };

    let commitment_hash = compute_order_commitment(&order_id, &secret);

    let order = Order {
        id: order_id,
        consumer,
        gpu_type,
        min_gpu_count: req.min_gpu_count,
        max_hourly_rate: req.max_hourly_rate,
        duration_hours: req.duration_hours,
        fill_constraints,
        status: OrderStatus::Committed,
        commitment_hash: Some(commitment_hash),
        created_at: current_height,
        settlement_id: None,
    };

    // Register the commitment in the fulfillment registry.
    let now = current_height; // Use block height as time proxy.
    match state
        .register_order_commitment(order_id, &secret, now)
        .await
    {
        Ok(_commitment) => {}
        Err(e) => {
            return (
                StatusCode::CONFLICT,
                Json(json!({"error": format!("commitment failed: {e}")})),
            );
        }
    }

    let id_hex = bytes32_to_hex(&order_id);
    info!(order_id = %id_hex, "order committed (sealed bid)");

    state.insert_order(order).await;

    (
        StatusCode::CREATED,
        Json(json!({
            "id": id_hex,
            "status": "committed",
            "commitment_hash": bytes32_to_hex(&commitment_hash)
        })),
    )
}

/// POST /orders/:id/reveal — reveal order details and trigger matching.
///
/// After the commit window elapses, the consumer reveals their secret.
/// This proves they committed first (anti-frontrunning) and triggers order matching.
async fn reveal_order(
    State(state): State<AppState>,
    Path(id): Path<String>,
    Json(req): Json<RevealOrderRequest>,
) -> impl IntoResponse {
    let order_id = match hex_to_bytes32(&id) {
        Ok(bytes) => bytes,
        Err(_) => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid order ID"})),
            )
                .into_response();
        }
    };

    let secret = match hex_to_bytes32(&req.secret) {
        Ok(s) => s,
        Err(_) => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "secret must be 64 hex chars (32 bytes)"})),
            )
                .into_response();
        }
    };

    let order = match state.get_order(&order_id).await {
        Some(o) => o,
        None => {
            return (
                StatusCode::NOT_FOUND,
                Json(json!({"error": "order not found"})),
            )
                .into_response();
        }
    };

    // Must be in committed state.
    if order.status != OrderStatus::Committed {
        return (
            StatusCode::CONFLICT,
            Json(json!({"error": "order is not in committed state"})),
        )
            .into_response();
    }

    // Validate the reveal against the commit-reveal registry.
    let now = state.current_height().await;
    if let Err(e) = state.validate_reveal(&order_id, &secret, now).await {
        return (
            StatusCode::FORBIDDEN,
            Json(json!({"error": format!("reveal rejected: {e}")})),
        )
            .into_response();
    }

    // Mark as revealed.
    state
        .update_order_status(&order_id, OrderStatus::Revealed)
        .await;

    // Attempt matching against available offerings.
    let offerings = state.list_offerings().await;
    let match_result = find_matching_offering(&order, &offerings);

    match match_result {
        Ok(matched) => {
            // Create settlement with atomic escrows.
            let offering = state.get_offering(&matched.offering_id).await.unwrap();
            let current_height = state.current_height().await;
            let timeout_height = current_height + DEFAULT_TIMEOUT_BLOCKS;
            let settlement_id = compute_settlement_id(
                &order.consumer,
                &offering.provider,
                &order_id,
                current_height,
            );

            let sla_bond_amount = matched.total_cost * SLA_BOND_PERCENTAGE / 100;

            // Create the pair of escrows atomically.
            let (payment_escrow, payment_escrow_id, sla_bond_escrow, sla_bond_escrow_id) =
                create_settlement_escrows(
                    &order.consumer,
                    &offering.provider,
                    matched.total_cost,
                    sla_bond_amount,
                    timeout_height,
                    &settlement_id,
                );

            // Store escrows.
            state.insert_escrow(payment_escrow_id, payment_escrow).await;
            state
                .insert_escrow(sla_bond_escrow_id, sla_bond_escrow)
                .await;

            // Create settlement record.
            let settlement = Settlement {
                id: settlement_id,
                consumer: order.consumer,
                provider: offering.provider,
                offering_id: matched.offering_id,
                order_id,
                payment_amount: matched.total_cost,
                sla_bond_amount,
                compute_hours: matched.fill_hours,
                payment_escrow_id,
                sla_bond_escrow_id,
                timeout_height,
                status: SettlementStatus::Active,
                created_at: current_height,
            };

            state.insert_settlement(settlement).await;

            // Update order status.
            let new_status = if matched.is_partial {
                let remaining = order.fill_constraints.max_fill_amount - matched.fill_hours;
                OrderStatus::PartiallyFilled {
                    filled_hours: matched.fill_hours,
                    remaining_hours: remaining,
                }
            } else {
                OrderStatus::Matched {
                    offering_id: matched.offering_id,
                }
            };
            state.update_order_status(&order_id, new_status).await;
            state.set_order_settlement(&order_id, settlement_id).await;
            state.mark_order_fulfilled(order_id).await;

            let id_hex = bytes32_to_hex(&order_id);
            info!(
                order_id = %id_hex,
                offering_id = %bytes32_to_hex(&matched.offering_id),
                fill_hours = matched.fill_hours,
                total_cost = matched.total_cost,
                "order matched and settlement created"
            );

            (
                StatusCode::OK,
                Json(json!({
                    "status": if matched.is_partial { "partially_filled" } else { "matched" },
                    "order_id": id_hex,
                    "settlement_id": bytes32_to_hex(&settlement_id),
                    "offering_id": bytes32_to_hex(&matched.offering_id),
                    "fill_hours": matched.fill_hours,
                    "total_cost": matched.total_cost,
                    "sla_bond": sla_bond_amount,
                    "timeout_height": timeout_height,
                })),
            )
                .into_response()
        }
        Err(e) => {
            // No match found. Order stays as revealed, can be matched later.
            info!(order_id = %bytes32_to_hex(&order_id), error = %e, "no matching offering found");
            (
                StatusCode::OK,
                Json(json!({
                    "status": "revealed",
                    "order_id": bytes32_to_hex(&order_id),
                    "match_error": e.to_string(),
                })),
            )
                .into_response()
        }
    }
}

/// GET /orders/:id — get order status.
async fn get_order(State(state): State<AppState>, Path(id): Path<String>) -> impl IntoResponse {
    let order_id = match hex_to_bytes32(&id) {
        Ok(bytes) => bytes,
        Err(_) => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid order ID"})),
            )
                .into_response();
        }
    };

    match state.get_order(&order_id).await {
        Some(order) => {
            let response = json!({
                "id": bytes32_to_hex(&order.id),
                "consumer": bytes32_to_hex(order.consumer.as_bytes()),
                "gpu_type": format!("{}", order.gpu_type),
                "min_gpu_count": order.min_gpu_count,
                "max_hourly_rate": order.max_hourly_rate,
                "duration_hours": order.duration_hours,
                "fill_constraints": {
                    "min_fill_hours": order.fill_constraints.min_fill_amount,
                    "max_fill_hours": order.fill_constraints.max_fill_amount,
                    "fill_or_kill": order.fill_constraints.fill_or_kill,
                },
                "status": format!("{:?}", order.status),
                "settlement_id": order.settlement_id.map(|s| bytes32_to_hex(&s)),
            });
            (StatusCode::OK, Json(response)).into_response()
        }
        None => (
            StatusCode::NOT_FOUND,
            Json(json!({"error": "order not found"})),
        )
            .into_response(),
    }
}

/// POST /settlements/:id/complete — provider claims payment with proof of delivery (LEGACY).
///
/// **DEPRECATED**: Use POST /settlements/:id/claim for the optimistic settlement flow.
///
/// This legacy endpoint requires STARK proof verification as the enforcement mechanism.
/// The newer optimistic flow (submit_claim -> dispute window -> finalize) is preferred
/// because it doesn't require the provider to generate an expensive ZK proof upfront.
/// Instead, the STARK proof becomes optional evidence that strengthens the claim.
///
/// The provider submits a ZK proof demonstrating they delivered the compute.
/// This triggers `ReleaseEscrow` on the payment escrow via `EscrowManager`.
async fn complete_settlement(
    State(state): State<AppState>,
    Path(id): Path<String>,
    Json(req): Json<CompleteSettlementRequest>,
) -> impl IntoResponse {
    let settlement_id = match hex_to_bytes32(&id) {
        Ok(bytes) => bytes,
        Err(_) => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid settlement ID"})),
            );
        }
    };

    let _provider = match cell_id_from_hex(&req.provider_cell) {
        Some(id) => id,
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid provider_cell hex"})),
            );
        }
    };

    let delivery_proof = match hex_decode(&req.delivery_proof) {
        Some(b) => b,
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid delivery_proof hex"})),
            );
        }
    };

    let settlement = match state.get_settlement(&settlement_id).await {
        Some(s) => s,
        None => {
            return (
                StatusCode::NOT_FOUND,
                Json(json!({"error": "settlement not found"})),
            );
        }
    };

    // Must be active.
    if settlement.status != SettlementStatus::Active {
        return (
            StatusCode::CONFLICT,
            Json(json!({"error": "settlement is not active"})),
        );
    }

    // Verify the provider identity matches.
    if bytes32_to_hex(settlement.provider.as_bytes()) != req.provider_cell {
        return (
            StatusCode::FORBIDDEN,
            Json(json!({"error": "only the provider can complete this settlement"})),
        );
    }

    // Verify the delivery proof CRYPTOGRAPHICALLY.
    //
    // The proof must:
    // 1. Deserialize as a valid StarkProof (DREG header)
    // 2. Have the expected AIR name for compute delivery proofs
    // 3. Be structurally complete (non-empty queries, valid trace length)
    // 4. PASS `stark::verify()` against the compute_delivery_descriptor() DSL circuit
    //    with public inputs derived from the settlement's contracted SLA parameters
    //
    // Steps 1-3 are structural pre-checks; step 4 is the cryptographic verification
    // that ensures the prover actually performed the contracted computation.
    // Without step 4, ANY non-empty byte sequence with the right header would be
    // accepted — a critical security vulnerability.

    // Reconstruct the SLA from the settlement's offering data.
    let offering = match state.get_offering(&settlement.offering_id).await {
        Some(o) => o,
        None => {
            error!(
                settlement_id = %bytes32_to_hex(&settlement_id),
                offering_id = %bytes32_to_hex(&settlement.offering_id),
                "settlement references missing offering (data integrity error)"
            );
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(json!({"error": "settlement references a missing offering"})),
            );
        }
    };

    let compute_sla =
        delivery_verification::ComputeSla::from_settlement(&settlement, &offering.sla);

    match delivery_verification::verify_delivery_proof(&delivery_proof, &compute_sla) {
        Ok(()) => {
            info!(
                settlement_id = %bytes32_to_hex(&settlement_id),
                compute_hours = settlement.compute_hours,
                "delivery proof cryptographically verified (STARK)"
            );
        }
        Err(e) => {
            warn!(
                settlement_id = %bytes32_to_hex(&settlement_id),
                error = %e,
                "delivery proof verification FAILED"
            );
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({
                    "error": format!("delivery proof rejected: {e}")
                })),
            );
        }
    }

    // Release the payment escrow via EscrowManager (provider gets paid).
    state
        .release_escrow(&settlement.payment_escrow_id, &delivery_proof)
        .await;
    // Release the SLA bond back to provider (successful delivery).
    state
        .release_escrow(&settlement.sla_bond_escrow_id, &delivery_proof)
        .await;

    // Update settlement status.
    state
        .update_settlement_status(&settlement_id, SettlementStatus::Completed)
        .await;

    // Update order status.
    state
        .update_order_status(&settlement.order_id, OrderStatus::Settled)
        .await;

    info!(
        settlement_id = %bytes32_to_hex(&settlement_id),
        "settlement completed, payment released to provider"
    );

    (
        StatusCode::OK,
        Json(json!({
            "status": "completed",
            "settlement_id": bytes32_to_hex(&settlement_id),
            "payment_released": settlement.payment_amount,
            "sla_bond_returned": settlement.sla_bond_amount,
        })),
    )
}

/// POST /disputes/:id — initiate a dispute against a settlement.
///
/// If the provider didn't deliver, the consumer can dispute.
/// If the timeout has passed, the consumer gets an automatic refund.
/// If the provider DID deliver, they can prove it via `ReleaseEscrow` with proof.
async fn create_dispute(
    State(state): State<AppState>,
    Path(id): Path<String>,
    Json(req): Json<CreateDisputeRequest>,
) -> impl IntoResponse {
    let settlement_id = match hex_to_bytes32(&id) {
        Ok(bytes) => bytes,
        Err(_) => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid settlement ID"})),
            );
        }
    };

    let initiator = match cell_id_from_hex(&req.initiator_cell) {
        Some(id) => id,
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid initiator_cell hex"})),
            );
        }
    };

    let settlement = match state.get_settlement(&settlement_id).await {
        Some(s) => s,
        None => {
            return (
                StatusCode::NOT_FOUND,
                Json(json!({"error": "settlement not found"})),
            );
        }
    };

    // Must be active to dispute.
    if settlement.status != SettlementStatus::Active {
        return (
            StatusCode::CONFLICT,
            Json(json!({"error": "settlement is not active (cannot dispute)"})),
        );
    }

    let current_height = state.current_height().await;

    // If timeout has passed, automatic refund via EscrowManager (consumer wins).
    if current_height >= settlement.timeout_height {
        // Refund escrows: consumer gets payment back, SLA bond forfeited to consumer.
        state
            .refund_escrow(&settlement.payment_escrow_id, current_height)
            .await;
        state
            .refund_escrow(&settlement.sla_bond_escrow_id, current_height)
            .await;

        state
            .update_settlement_status(&settlement_id, SettlementStatus::Refunded)
            .await;

        let dispute = Dispute {
            settlement_id,
            initiator,
            reason: req.reason,
            status: DisputeStatus::ResolvedForConsumer,
            filed_at: current_height,
        };
        state.insert_dispute(dispute).await;

        info!(
            settlement_id = %bytes32_to_hex(&settlement_id),
            "dispute auto-resolved: timeout passed, consumer refunded"
        );

        return (
            StatusCode::OK,
            Json(json!({
                "status": "resolved_for_consumer",
                "settlement_id": bytes32_to_hex(&settlement_id),
                "reason": "timeout_expired",
                "refunded_amount": settlement.payment_amount,
                "sla_bond_forfeited": settlement.sla_bond_amount,
            })),
        );
    }

    // Timeout hasn't passed: open the dispute for resolution.
    state
        .update_settlement_status(&settlement_id, SettlementStatus::Disputed)
        .await;

    let dispute = Dispute {
        settlement_id,
        initiator,
        reason: req.reason.clone(),
        status: DisputeStatus::Open,
        filed_at: current_height,
    };
    state.insert_dispute(dispute).await;

    info!(
        settlement_id = %bytes32_to_hex(&settlement_id),
        reason = %req.reason,
        "dispute opened"
    );

    (
        StatusCode::OK,
        Json(json!({
            "status": "disputed",
            "settlement_id": bytes32_to_hex(&settlement_id),
            "timeout_height": settlement.timeout_height,
            "current_height": current_height,
            "blocks_until_timeout": settlement.timeout_height - current_height,
        })),
    )
}

// =============================================================================
// Optimistic Settlement Handlers
// =============================================================================

/// The dispute configuration for the compute exchange.
/// 100 blocks dispute window, 10% challenger stake, tiered arbiter.
fn compute_exchange_dispute_config() -> DisputeConfig {
    DisputeConfig {
        dispute_window_blocks: 100, // ~20 minutes at 12s blocks
        challenger_stake_pct: 10,
        arbiter_strategy: dregg_app_framework::dispute::ArbiterStrategy::Tiered {
            cryptographic_deadline_blocks: 200,
            federation_quorum: 3,
            federation_deadline_blocks: 500,
        },
        winner_slash_pct: 80,
        require_proof_in_claim: false, // STARK proof is optional evidence
    }
}

/// POST /settlements/:id/claim — provider submits a delivery claim (optimistic).
///
/// Instead of requiring STARK verification as enforcement, the provider submits
/// a signed attestation of delivery metrics. The STARK proof is OPTIONAL EVIDENCE
/// that strengthens the claim but is not the enforcement mechanism.
///
/// After submission, a dispute window opens. If no challenge arrives before the
/// deadline, the settlement is finalized (payment released, stake returned).
async fn submit_claim(
    State(state): State<AppState>,
    Path(id): Path<String>,
    Json(req): Json<SubmitClaimRequest>,
) -> impl IntoResponse {
    let settlement_id = match hex_to_bytes32(&id) {
        Ok(bytes) => bytes,
        Err(_) => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid settlement ID"})),
            );
        }
    };

    let provider = match cell_id_from_hex(&req.provider_cell) {
        Some(id) => id,
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid provider_cell hex"})),
            );
        }
    };

    let output_hash = match hex_to_bytes32(&req.output_hash) {
        Ok(h) => h,
        Err(_) => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid output_hash hex"})),
            );
        }
    };

    let settlement = match state.get_settlement(&settlement_id).await {
        Some(s) => s,
        None => {
            return (
                StatusCode::NOT_FOUND,
                Json(json!({"error": "settlement not found"})),
            );
        }
    };

    // Must be active.
    if settlement.status != SettlementStatus::Active {
        return (
            StatusCode::CONFLICT,
            Json(json!({"error": "settlement is not active"})),
        );
    }

    // Verify the provider identity matches.
    if settlement.provider != provider {
        return (
            StatusCode::FORBIDDEN,
            Json(json!({"error": "only the provider can submit a claim"})),
        );
    }

    // Parse optional fields.
    let input_hash = req.input_hash.as_ref().and_then(|h| hex_to_bytes32(h).ok());

    let signature = match hex_decode(&req.signature) {
        Some(sig) if sig.len() == 64 => {
            let mut arr = [0u8; 64];
            arr.copy_from_slice(&sig);
            arr
        }
        _ => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "signature must be 128 hex chars (64 bytes)"})),
            );
        }
    };

    let delivery_proof = req.delivery_proof.as_ref().and_then(|p| hex_decode(p));

    // If a STARK proof is provided, validate it as EVIDENCE (not enforcement).
    // A valid proof strengthens the claim. An invalid proof is suspicious but
    // doesn't block the claim — the dispute window handles enforcement.
    let proof_verified = if let Some(ref proof_bytes) = delivery_proof {
        let offering = state.get_offering(&settlement.offering_id).await;
        if let Some(offering) = offering {
            let sla =
                delivery_verification::ComputeSla::from_settlement(&settlement, &offering.sla);
            match delivery_verification::verify_delivery_proof(proof_bytes, &sla) {
                Ok(()) => {
                    info!(
                        settlement_id = %bytes32_to_hex(&settlement_id),
                        "optional STARK proof verified (strengthens claim)"
                    );
                    true
                }
                Err(e) => {
                    warn!(
                        settlement_id = %bytes32_to_hex(&settlement_id),
                        error = %e,
                        "optional STARK proof FAILED verification (claim still accepted, evidence weak)"
                    );
                    false
                }
            }
        } else {
            false
        }
    } else {
        false
    };

    // Compute the dispute deadline.
    let current_height = state.current_height().await;
    let config = compute_exchange_dispute_config();
    let dispute_deadline = current_height + config.dispute_window_blocks;

    // Build the delivery claim.
    let metrics = ComputeMetrics {
        flops_delivered: req.flops_delivered,
        duration_seconds: req.duration_seconds,
        quality_bps: req.quality_bps,
        output_hash,
        input_hash,
    };

    let metrics_payload = serde_json::to_vec(&metrics).unwrap_or_default();
    let proof_included = delivery_proof.is_some();

    let claim = DeliveryClaim {
        metrics_payload,
        signature,
        proof: delivery_proof,
    };

    // Build the optimistic settlement record.
    let opt_settlement_id = dispute_framework::compute_settlement_id(
        &settlement.sla_bond_escrow_id, // obligation backing the stake
        &provider,
        &settlement.consumer,
        current_height,
    );

    // TODO: persist this in a dedicated ContentStore<OptimisticSettlement<DeliveryClaim>>
    // once the full dispute lifecycle is wired through state.rs.
    let _opt_settlement: OptimisticSettlement<DeliveryClaim> = OptimisticSettlement {
        id: opt_settlement_id,
        obligation_id: settlement.sla_bond_escrow_id,
        claimant: provider,
        counterparty: settlement.consumer,
        claim,
        dispute_deadline,
        state: OptimisticState::Pending {
            submitted_at: current_height,
        },
        stake_amount: settlement.sla_bond_amount,
        payment_amount: settlement.payment_amount,
    };

    // Transition the settlement to a "claim pending" state.
    // We reuse the existing Completed status with a note that it's optimistic.
    // In a full implementation, SettlementStatus would have a ClaimPending variant.
    state
        .update_settlement_status(&settlement_id, SettlementStatus::Completed)
        .await;

    info!(
        settlement_id = %bytes32_to_hex(&settlement_id),
        dispute_deadline = dispute_deadline,
        proof_included = proof_included,
        proof_verified = proof_verified,
        "delivery claim submitted (optimistic), dispute window open"
    );

    (
        StatusCode::OK,
        Json(json!({
            "status": "claim_pending",
            "settlement_id": bytes32_to_hex(&settlement_id),
            "optimistic_settlement_id": bytes32_to_hex(&opt_settlement_id),
            "dispute_deadline": dispute_deadline,
            "current_height": current_height,
            "blocks_until_finalization": config.dispute_window_blocks,
            "proof_included": req.delivery_proof.is_some(),
            "proof_verified": proof_verified,
            "metrics": {
                "flops_delivered": req.flops_delivered,
                "duration_seconds": req.duration_seconds,
                "quality_bps": req.quality_bps,
                "output_hash": req.output_hash,
            },
        })),
    )
}

/// POST /settlements/:id/challenge — challenge a pending delivery claim.
///
/// The challenger must stake (to prevent frivolous disputes) and provide evidence.
/// If the challenge succeeds: provider's stake is slashed, challenger receives reward.
/// If the challenge fails: challenger's stake goes to the provider.
async fn challenge_claim(
    State(state): State<AppState>,
    Path(id): Path<String>,
    Json(req): Json<ChallengeClaimRequest>,
) -> impl IntoResponse {
    let settlement_id = match hex_to_bytes32(&id) {
        Ok(bytes) => bytes,
        Err(_) => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid settlement ID"})),
            );
        }
    };

    let challenger = match cell_id_from_hex(&req.challenger_cell) {
        Some(id) => id,
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid challenger_cell hex"})),
            );
        }
    };

    let settlement = match state.get_settlement(&settlement_id).await {
        Some(s) => s,
        None => {
            return (
                StatusCode::NOT_FOUND,
                Json(json!({"error": "settlement not found"})),
            );
        }
    };

    // Must be in Completed state (which means claim was submitted in optimistic flow).
    if settlement.status != SettlementStatus::Completed {
        return (
            StatusCode::CONFLICT,
            Json(json!({"error": "settlement has no pending claim to challenge"})),
        );
    }

    // Check the dispute window is still open.
    let current_height = state.current_height().await;
    let config = compute_exchange_dispute_config();
    // Dispute deadline = settlement.created_at + DEFAULT_TIMEOUT_BLOCKS (we use timeout_height).
    // For the optimistic flow, the dispute window is from claim submission.
    // Since we don't store the claim time separately yet, use timeout_height as proxy.
    if current_height >= settlement.timeout_height {
        return (
            StatusCode::CONFLICT,
            Json(json!({
                "error": "dispute window has closed",
                "deadline": settlement.timeout_height,
                "current_height": current_height,
            })),
        );
    }

    // Check challenger stake meets minimum.
    let min_stake =
        dispute_framework::minimum_challenger_stake(settlement.sla_bond_amount, &config);
    if req.challenger_stake < min_stake {
        return (
            StatusCode::BAD_REQUEST,
            Json(json!({
                "error": "insufficient challenger stake",
                "required": min_stake,
                "provided": req.challenger_stake,
            })),
        );
    }

    // Parse the evidence.
    let evidence = match req.evidence_type.as_str() {
        "re_execution_mismatch" => {
            let claimed = req.evidence_payload["claimed_output_hash"]
                .as_str()
                .and_then(|h| hex_to_bytes32(h).ok())
                .unwrap_or([0u8; 32]);
            let actual = req.evidence_payload["actual_output_hash"]
                .as_str()
                .and_then(|h| hex_to_bytes32(h).ok())
                .unwrap_or([0u8; 32]);
            let proof = req.evidence_payload["execution_proof"]
                .as_str()
                .and_then(|p| hex_decode(p));
            DisputeEvidence::ReExecutionMismatch {
                claimed_output_hash: claimed,
                actual_output_hash: actual,
                execution_proof: proof,
            }
        }
        "proof_invalid" => {
            let error = req.evidence_payload["verification_error"]
                .as_str()
                .unwrap_or("unspecified")
                .to_string();
            DisputeEvidence::ProofInvalid {
                verification_error: error,
            }
        }
        "metrics_impossible" => {
            let reason = req.evidence_payload["reason"]
                .as_str()
                .unwrap_or("unspecified")
                .to_string();
            let max_flops = req.evidence_payload["max_possible_flops"]
                .as_u64()
                .unwrap_or(0);
            DisputeEvidence::MetricsImpossible {
                reason,
                max_possible_flops: max_flops,
            }
        }
        "uptime_violation" => {
            let blocks: Vec<u64> = req.evidence_payload["missed_blocks"]
                .as_array()
                .map(|arr| arr.iter().filter_map(|v| v.as_u64()).collect())
                .unwrap_or_default();
            let required = req.evidence_payload["required_uptime_bps"]
                .as_u64()
                .unwrap_or(9500) as u32;
            let actual = req.evidence_payload["actual_uptime_bps"]
                .as_u64()
                .unwrap_or(0) as u32;
            DisputeEvidence::UptimeViolation {
                missed_heartbeat_blocks: blocks,
                required_uptime_bps: required,
                actual_uptime_bps: actual,
            }
        }
        other => {
            let payload = serde_json::to_vec(&req.evidence_payload).unwrap_or_default();
            DisputeEvidence::Custom {
                evidence_type: other.to_string(),
                payload,
            }
        }
    };

    // Validate evidence structure.
    if let Err(e) = dispute_framework::validate_evidence_structure(&evidence) {
        return (
            StatusCode::BAD_REQUEST,
            Json(json!({"error": format!("invalid evidence: {e}")})),
        );
    }

    // Compute dispute ID.
    let dispute_id =
        dispute_framework::compute_dispute_id(&settlement_id, &challenger, current_height);

    // Transition the settlement to disputed.
    state
        .update_settlement_status(&settlement_id, SettlementStatus::Disputed)
        .await;

    // Create the dispute record (using the existing Dispute struct for backward compat).
    let dispute = Dispute {
        settlement_id,
        initiator: challenger,
        reason: format!("challenge:{}", req.evidence_type),
        status: DisputeStatus::Open,
        filed_at: current_height,
    };
    state.insert_dispute(dispute).await;

    info!(
        settlement_id = %bytes32_to_hex(&settlement_id),
        challenger = %bytes32_to_hex(challenger.as_bytes()),
        evidence_type = %req.evidence_type,
        challenger_stake = req.challenger_stake,
        "claim challenged, dispute opened"
    );

    (
        StatusCode::OK,
        Json(json!({
            "status": "disputed",
            "settlement_id": bytes32_to_hex(&settlement_id),
            "dispute_id": bytes32_to_hex(&dispute_id),
            "evidence_type": req.evidence_type,
            "challenger_stake": req.challenger_stake,
            "min_stake_required": min_stake,
            "resolution_strategy": "tiered (cryptographic -> federation)",
        })),
    )
}

/// POST /settlements/:id/finalize — finalize an unchallenged settlement.
///
/// Called after the dispute window closes with no challenge. Releases payment
/// to the provider and returns their stake.
///
/// Anyone can call this (it's permissionless after the window closes), but
/// typically the provider calls it to claim their payment.
async fn finalize_settlement(
    State(state): State<AppState>,
    Path(id): Path<String>,
    Json(req): Json<FinalizeSettlementRequest>,
) -> impl IntoResponse {
    let settlement_id = match hex_to_bytes32(&id) {
        Ok(bytes) => bytes,
        Err(_) => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid settlement ID"})),
            );
        }
    };

    let _requestor = match cell_id_from_hex(&req.requestor_cell) {
        Some(id) => id,
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid requestor_cell hex"})),
            );
        }
    };

    let settlement = match state.get_settlement(&settlement_id).await {
        Some(s) => s,
        None => {
            return (
                StatusCode::NOT_FOUND,
                Json(json!({"error": "settlement not found"})),
            );
        }
    };

    // Must be in Completed state (claim submitted, no dispute).
    if settlement.status != SettlementStatus::Completed {
        return (
            StatusCode::CONFLICT,
            Json(json!({
                "error": "settlement cannot be finalized (not in claim-pending state)",
                "current_status": format!("{:?}", settlement.status),
            })),
        );
    }

    // Check the dispute window has closed.
    let current_height = state.current_height().await;
    if current_height < settlement.timeout_height {
        return (
            StatusCode::CONFLICT,
            Json(json!({
                "error": "dispute window still open",
                "deadline": settlement.timeout_height,
                "current_height": current_height,
                "blocks_remaining": settlement.timeout_height - current_height,
            })),
        );
    }

    // Dispute window closed without challenge. Finalize:
    // 1. Release payment escrow to provider.
    // 2. Return SLA bond to provider.
    state
        .release_escrow(&settlement.payment_escrow_id, &[])
        .await;
    state
        .release_escrow(&settlement.sla_bond_escrow_id, &[])
        .await;

    // Update order status.
    state
        .update_order_status(&settlement.order_id, OrderStatus::Settled)
        .await;

    info!(
        settlement_id = %bytes32_to_hex(&settlement_id),
        payment = settlement.payment_amount,
        stake_returned = settlement.sla_bond_amount,
        "settlement finalized (unchallenged), payment released to provider"
    );

    (
        StatusCode::OK,
        Json(json!({
            "status": "finalized",
            "settlement_id": bytes32_to_hex(&settlement_id),
            "payment_released": settlement.payment_amount,
            "stake_returned": settlement.sla_bond_amount,
            "finalized_at_height": current_height,
        })),
    )
}

/// GET /health — health check.
async fn health_check() -> impl IntoResponse {
    Json(json!({"status": "ok", "service": "compute-exchange"}))
}

/// Verify admin bearer token from the `Authorization` header.
/// Returns `Err(Response)` with 401 if the token is missing or invalid.
fn check_admin_auth(headers: &HeaderMap) -> Result<(), (StatusCode, Json<serde_json::Value>)> {
    let expected_token = std::env::var("DREGG_ADMIN_TOKEN").unwrap_or_default();
    if expected_token.is_empty() {
        // No token configured — admin endpoints are unprotected (dev mode).
        return Ok(());
    }

    let auth_header = headers
        .get("authorization")
        .and_then(|v| v.to_str().ok())
        .unwrap_or("");

    let provided_token = auth_header.strip_prefix("Bearer ").unwrap_or("");
    if provided_token.is_empty() || provided_token != expected_token {
        return Err((
            StatusCode::UNAUTHORIZED,
            Json(json!({"error": "unauthorized: invalid or missing admin token"})),
        ));
    }

    Ok(())
}

/// POST /admin/height — advance the simulated block height.
async fn advance_height(
    headers: HeaderMap,
    State(state): State<AppState>,
    Json(body): Json<serde_json::Value>,
) -> impl IntoResponse {
    if let Err(e) = check_admin_auth(&headers) {
        return e.into_response();
    }
    let delta = body["delta"].as_u64().unwrap_or(1);
    state.advance_height(delta).await;
    let new_height = state.current_height().await;
    Json(json!({"height": new_height})).into_response()
}

/// POST /admin/federation-root — set the federation root at runtime.
///
/// Accepts JSON: `{"root": "abcd...1234"}` (64 hex chars).
async fn admin_set_federation_root(
    headers: HeaderMap,
    State(state): State<AppState>,
    Json(body): Json<serde_json::Value>,
) -> impl IntoResponse {
    if let Err(e) = check_admin_auth(&headers) {
        return e.into_response();
    }
    let root_hex = match body["root"].as_str() {
        Some(s) => s,
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "missing 'root' field (64 hex chars)"})),
            )
                .into_response();
        }
    };

    let root_hex = root_hex.strip_prefix("0x").unwrap_or(root_hex);
    match hex_to_bytes32(root_hex) {
        Ok(root) => {
            if root == [0u8; 32] {
                return (
                    StatusCode::BAD_REQUEST,
                    Json(json!({"error": "refusing to set all-zeroes federation root"})),
                )
                    .into_response();
            }
            state.set_federation_root(root).await;
            info!(root = %bytes32_to_hex(&root), "federation root updated via admin endpoint");
            (StatusCode::OK, Json(json!({"root": bytes32_to_hex(&root)}))).into_response()
        }
        Err(_) => (
            StatusCode::BAD_REQUEST,
            Json(json!({"error": "invalid root hex (expected 64 hex chars)"})),
        )
            .into_response(),
    }
}

// =============================================================================
// Helpers
// =============================================================================

/// Parse a GPU type string into the enum.
fn parse_gpu_type(s: &str) -> GpuType {
    match s {
        "A100" => GpuType::A100,
        "H100" => GpuType::H100,
        "H200" => GpuType::H200,
        "L40S" => GpuType::L40S,
        "RTX4090" => GpuType::RTX4090,
        other => GpuType::Custom(other.to_string()),
    }
}

/// Decode a hex string to a CellId.
fn cell_id_from_hex(hex: &str) -> Option<CellId> {
    let bytes = hex_to_bytes32(hex).ok()?;
    Some(CellId::from_bytes(bytes))
}

/// Decode a hex string to a Vec<u8> (variable length).
fn hex_decode(hex: &str) -> Option<Vec<u8>> {
    if hex.len() % 2 != 0 {
        return None;
    }
    let mut out = Vec::with_capacity(hex.len() / 2);
    for chunk in hex.as_bytes().chunks(2) {
        let high = hex_nibble(chunk[0])?;
        let low = hex_nibble(chunk[1])?;
        out.push((high << 4) | low);
    }
    Some(out)
}

fn hex_nibble(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b - b'0'),
        b'a'..=b'f' => Some(b - b'a' + 10),
        b'A'..=b'F' => Some(b - b'A' + 10),
        _ => None,
    }
}
