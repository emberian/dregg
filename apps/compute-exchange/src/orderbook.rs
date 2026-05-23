//! Order book and matching logic for compute offerings and orders.
//!
//! Providers list offerings with GPU specs, rates, and availability.
//! Consumers place orders with requirements and fill constraints.
//! The matcher finds compatible offerings and executes partial fills when applicable.

use pyana_app_framework::{CellId, FillConstraints};
use pyana_intent::partial_fill::{PartialFillError, check_fill_amount};
use serde::{Deserialize, Serialize};

// =============================================================================
// Types
// =============================================================================

/// Unique identifier for an order.
pub type OrderId = [u8; 32];

/// GPU type offered by a compute provider.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum GpuType {
    A100,
    H100,
    H200,
    L40S,
    RTX4090,
    Custom(String),
}

impl std::fmt::Display for GpuType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::A100 => write!(f, "A100"),
            Self::H100 => write!(f, "H100"),
            Self::H200 => write!(f, "H200"),
            Self::L40S => write!(f, "L40S"),
            Self::RTX4090 => write!(f, "RTX4090"),
            Self::Custom(s) => write!(f, "{}", s),
        }
    }
}

/// SLA guarantees from a compute provider.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SlaGuarantees {
    /// Minimum uptime percentage (e.g., 99.9 = 999 in basis points out of 1000).
    pub uptime_bps: u32,
    /// Maximum latency in milliseconds for the first response.
    pub max_latency_ms: u32,
    /// Whether the provider supports preemption recovery.
    pub preemption_recovery: bool,
}

/// A compute offering posted by a provider.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Offering {
    /// Content-addressed offering ID.
    pub id: [u8; 32],
    /// The provider's cell identity.
    pub provider: CellId,
    /// GPU type being offered.
    pub gpu_type: GpuType,
    /// Number of GPUs available.
    pub gpu_count: u32,
    /// Hourly rate in the exchange's unit (smallest denomination).
    pub hourly_rate: u64,
    /// How many hours of availability remain.
    pub available_hours: u64,
    /// SLA guarantees.
    pub sla: SlaGuarantees,
    /// Whether this offering is currently available for matching.
    pub available: bool,
    /// Block height when this offering was created.
    pub created_at: u64,
    /// Optional qualification proof hash (e.g., provider proved >= N GPUs).
    pub qualification_proof_hash: Option<[u8; 32]>,
}

/// An order placed by a compute consumer.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Order {
    /// Content-addressed order ID.
    pub id: OrderId,
    /// The consumer's cell identity.
    pub consumer: CellId,
    /// Required GPU type.
    pub gpu_type: GpuType,
    /// Minimum GPUs needed.
    pub min_gpu_count: u32,
    /// Maximum price willing to pay per hour.
    pub max_hourly_rate: u64,
    /// Duration needed in hours.
    pub duration_hours: u64,
    /// Fill constraints: min/max compute-hours, fill-or-kill behavior.
    pub fill_constraints: FillConstraints,
    /// Current order status.
    pub status: OrderStatus,
    /// The commit-reveal commitment hash (set during commit phase).
    pub commitment_hash: Option<[u8; 32]>,
    /// Block height when this order was placed.
    pub created_at: u64,
    /// Associated settlement ID (set after matching).
    pub settlement_id: Option<[u8; 32]>,
}

/// Order lifecycle status.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum OrderStatus {
    /// Committed but not yet revealed (anti-frontrunning).
    Committed,
    /// Revealed and waiting for matching.
    Revealed,
    /// Matched with an offering, settlement in progress.
    Matched { offering_id: [u8; 32] },
    /// Partially filled (some compute-hours allocated).
    PartiallyFilled {
        filled_hours: u64,
        remaining_hours: u64,
    },
    /// Fully filled and settled.
    Settled,
    /// Order was cancelled or expired.
    Cancelled,
}

// =============================================================================
// Matching logic
// =============================================================================

/// Result of matching an order against the available offerings.
#[derive(Clone, Debug)]
pub struct MatchResult {
    /// The offering that matches.
    pub offering_id: [u8; 32],
    /// How many compute-hours will be filled.
    pub fill_hours: u64,
    /// Total cost for the filled hours.
    pub total_cost: u64,
    /// Whether this is a partial fill (vs complete).
    pub is_partial: bool,
}

/// Find the best matching offering for an order.
///
/// Match criteria:
/// - GPU type must match
/// - Offering must have >= min_gpu_count GPUs
/// - Offering rate must be <= order's max rate
/// - Offering must have available hours
///
/// When multiple offerings match, prefer: lowest rate first, then most availability.
pub fn find_matching_offering(
    order: &Order,
    offerings: &[Offering],
) -> Result<MatchResult, MatchError> {
    let mut candidates: Vec<&Offering> = offerings
        .iter()
        .filter(|o| {
            o.available
                && o.gpu_type == order.gpu_type
                && o.gpu_count >= order.min_gpu_count
                && o.hourly_rate <= order.max_hourly_rate
                && o.available_hours > 0
        })
        .collect();

    if candidates.is_empty() {
        return Err(MatchError::NoMatchingOffering);
    }

    // Sort by rate (ascending), then by available hours (descending).
    candidates.sort_by(|a, b| {
        a.hourly_rate
            .cmp(&b.hourly_rate)
            .then(b.available_hours.cmp(&a.available_hours))
    });

    let best = candidates[0];

    // Determine how many hours we can fill.
    let available_hours = best.available_hours;
    let effective_hours =
        check_fill_amount(&order.fill_constraints, available_hours).map_err(|e| match e {
            PartialFillError::BelowMinimum { available, minimum } => {
                MatchError::InsufficientCapacity { available, minimum }
            }
            PartialFillError::FillOrKillRejected {
                available,
                required,
            } => MatchError::FillOrKillFailed {
                available,
                required,
            },
            _ => MatchError::NoMatchingOffering,
        })?;

    let is_partial = effective_hours < order.fill_constraints.max_fill_amount;
    let total_cost = effective_hours * best.hourly_rate;

    Ok(MatchResult {
        offering_id: best.id,
        fill_hours: effective_hours,
        total_cost,
        is_partial,
    })
}

/// Errors during order matching.
#[derive(Clone, Debug)]
pub enum MatchError {
    /// No offering matches the order's requirements.
    NoMatchingOffering,
    /// Available capacity is below the order's minimum.
    InsufficientCapacity { available: u64, minimum: u64 },
    /// Fill-or-kill order cannot be fully satisfied.
    FillOrKillFailed { available: u64, required: u64 },
}

impl std::fmt::Display for MatchError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoMatchingOffering => write!(f, "no matching offering found"),
            Self::InsufficientCapacity { available, minimum } => {
                write!(
                    f,
                    "insufficient capacity: {} hours available, {} required",
                    available, minimum
                )
            }
            Self::FillOrKillFailed {
                available,
                required,
            } => {
                write!(
                    f,
                    "fill-or-kill: only {} hours available, {} required",
                    available, required
                )
            }
        }
    }
}

// =============================================================================
// ID computation
// =============================================================================

/// Compute a content-addressed offering ID.
pub fn compute_offering_id(
    provider: &CellId,
    gpu_type: &GpuType,
    hourly_rate: u64,
    created_at: u64,
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("compute-exchange-offering-v1");
    hasher.update(provider.as_bytes());
    hasher.update(gpu_type.to_string().as_bytes());
    hasher.update(&hourly_rate.to_le_bytes());
    hasher.update(&created_at.to_le_bytes());
    *hasher.finalize().as_bytes()
}

/// Compute a content-addressed order ID.
pub fn compute_order_id(
    consumer: &CellId,
    gpu_type: &GpuType,
    max_hourly_rate: u64,
    created_at: u64,
) -> OrderId {
    let mut hasher = blake3::Hasher::new_derive_key("compute-exchange-order-v1");
    hasher.update(consumer.as_bytes());
    hasher.update(gpu_type.to_string().as_bytes());
    hasher.update(&max_hourly_rate.to_le_bytes());
    hasher.update(&created_at.to_le_bytes());
    *hasher.finalize().as_bytes()
}
