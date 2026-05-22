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

mod auction;
mod orderbook;
mod qualification;
mod settlement;
mod state;

use std::net::SocketAddr;

use axum::{
    Json, Router,
    extract::{Path, State},
    http::StatusCode,
    response::IntoResponse,
    routing::{get, post},
};
use clap::Parser;
use serde::{Deserialize, Serialize};
use serde_json::json;
use tracing::{error, info, warn};

use pyana_app_framework::hex::{bytes32_to_hex, hex_to_bytes32};
use pyana_app_framework::{CellId, FillConstraints};

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
    /// Federation root hash (64 hex chars). If not provided, fetches from a federation node.
    #[arg(long, env = "PYANA_FEDERATION_ROOT")]
    federation_root: Option<String>,

    /// Federation node URL to sync root from (not yet implemented).
    #[arg(long, env = "PYANA_FEDERATION_NODE")]
    federation_node: Option<String>,

    /// Run in dev mode: allows starting with an all-zeroes federation root.
    /// WARNING: proof verification will reject all federation membership proofs.
    #[arg(long, env = "PYANA_DEV")]
    dev: bool,

    /// Listen address.
    #[arg(long, default_value = "127.0.0.1:3040", env = "PYANA_LISTEN")]
    listen: SocketAddr,
}

// =============================================================================
// Main
// =============================================================================

/// Parse a 64-char hex string into a [u8; 32] federation root.
fn parse_federation_root(hex: &str) -> Result<[u8; 32], String> {
    let hex = hex.strip_prefix("0x").unwrap_or(hex);
    hex_to_bytes32(hex).map_err(|e| format!("invalid federation root hex: {e}"))
}

#[tokio::main]
async fn main() {
    tracing_subscriber::fmt()
        .with_target(false)
        .with_level(true)
        .init();

    let args = Args::parse();

    // Resolve federation root.
    let federation_root = match &args.federation_root {
        Some(hex) => match parse_federation_root(hex) {
            Ok(root) => {
                info!(
                    root = %bytes32_to_hex(&root),
                    "federation root configured (from PYANA_FEDERATION_ROOT)"
                );
                root
            }
            Err(e) => {
                error!("{e}");
                std::process::exit(1);
            }
        },
        None => {
            if args.dev {
                warn!(
                    "running in --dev mode with zeroed federation root; federation membership proofs will be rejected"
                );
                [0u8; 32]
            } else {
                error!(
                    "no federation root configured. Set PYANA_FEDERATION_ROOT or --federation-root, or use --dev for testing without verification."
                );
                std::process::exit(1);
            }
        }
    };

    let state = AppState::with_federation_root(federation_root);

    let app = Router::new()
        // Offering lifecycle
        .route("/offerings", post(create_offering))
        .route("/offerings", get(list_offerings))
        // Order lifecycle (commit-reveal)
        .route("/orders", post(create_order))
        .route("/orders/{id}/reveal", post(reveal_order))
        .route("/orders/{id}", get(get_order))
        // Settlement
        .route("/settlements/{id}/complete", post(complete_settlement))
        // Disputes
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

/// POST /settlements/:id/complete — provider claims payment with proof of delivery.
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

    // Verify the delivery proof is non-empty (in production: full STARK verification).
    if delivery_proof.is_empty() {
        return (
            StatusCode::BAD_REQUEST,
            Json(json!({"error": "delivery proof must not be empty"})),
        );
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

/// GET /health — health check.
async fn health_check() -> impl IntoResponse {
    Json(json!({"status": "ok", "service": "compute-exchange"}))
}

/// POST /admin/height — advance the simulated block height.
async fn advance_height(
    State(state): State<AppState>,
    Json(body): Json<serde_json::Value>,
) -> impl IntoResponse {
    let delta = body["delta"].as_u64().unwrap_or(1);
    state.advance_height(delta).await;
    let new_height = state.current_height().await;
    Json(json!({"height": new_height}))
}

/// POST /admin/federation-root — set the federation root at runtime.
///
/// Accepts JSON: `{"root": "abcd...1234"}` (64 hex chars).
async fn admin_set_federation_root(
    State(state): State<AppState>,
    Json(body): Json<serde_json::Value>,
) -> impl IntoResponse {
    let root_hex = match body["root"].as_str() {
        Some(s) => s,
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "missing 'root' field (64 hex chars)"})),
            );
        }
    };

    let root_hex = root_hex.strip_prefix("0x").unwrap_or(root_hex);
    match hex_to_bytes32(root_hex) {
        Ok(root) => {
            if root == [0u8; 32] {
                return (
                    StatusCode::BAD_REQUEST,
                    Json(json!({"error": "refusing to set all-zeroes federation root"})),
                );
            }
            state.set_federation_root(root).await;
            info!(root = %bytes32_to_hex(&root), "federation root updated via admin endpoint");
            (StatusCode::OK, Json(json!({"root": bytes32_to_hex(&root)})))
        }
        Err(_) => (
            StatusCode::BAD_REQUEST,
            Json(json!({"error": "invalid root hex (expected 64 hex chars)"})),
        ),
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
