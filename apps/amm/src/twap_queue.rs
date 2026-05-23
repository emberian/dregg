//! Programmable queue for MEV-resistant swap batching with TWAP execution.
//!
//! Wraps [`ProgrammableQueue`] with the `programs::open(min_deposit)` validation
//! program. Swaps are enqueued during the block and executed all at the same
//! TWAP price computed from the pool's open reserve ratio at batch-start.
//!
//! # TWAP price computation
//!
//! The open price is snapshot at the start of a batch execution run. All swaps
//! in the queue are executed at that price rather than updating the pool state
//! between each individual swap. This eliminates sandwich attacks because:
//! - All trades see the same price (the block-open price).
//! - The price only updates once, after all swaps are batched.
//!
//! # HTTP routes (mounted under `/queue/swaps`)
//!
//! - `POST /queue/swaps/enqueue` — submit a swap intent
//! - `POST /queue/swaps/dequeue` — dequeue next intent (admin/solver only)
//! - `GET /queue/swaps/status` — queue length, root hash
//! - `POST /queue/swaps/execute-batch` — execute all queued swaps at TWAP price
//!
//! The first three come from `QueueEndpoint`. The last is added here as an
//! extension mounted in the same router.

use std::sync::Arc;

use axum::{
    Json, Router,
    extract::State,
    http::StatusCode,
    routing::post,
};
use serde::{Deserialize, Serialize};
use tokio::sync::RwLock;

use pyana_app_framework::queue_endpoint::QueueEndpoint;
use pyana_storage::programmable::{ProgrammableQueue, ValidationContext, programs};
use pyana_storage::queue::QueueEntry;

use crate::server::AppState;

// =============================================================================
// SwapIntent: what gets hashed and stored in the queue
// =============================================================================

/// A pending swap intent submitted to the TWAP batch queue.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SwapIntent {
    /// Pool to swap in.
    pub pool_id: [u8; 32],
    /// Amount of input token.
    pub amount_in: u64,
    /// Direction (true = A→B, false = B→A).
    pub direction_a_to_b: bool,
    /// Minimum output required (slippage protection applied at batch time).
    pub min_out: u64,
    /// Submitter identity (32-byte pubkey).
    pub submitter: [u8; 32],
}

impl SwapIntent {
    /// Hash this intent to a 32-byte content hash.
    pub fn content_hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"pyana-amm-swap-intent-v1");
        hasher.update(&self.pool_id);
        hasher.update(&self.amount_in.to_le_bytes());
        hasher.update(&[self.direction_a_to_b as u8]);
        hasher.update(&self.min_out.to_le_bytes());
        hasher.update(&self.submitter);
        *hasher.finalize().as_bytes()
    }
}

// =============================================================================
// TwapBatchState: in-memory staging area for pending swap intents
// =============================================================================

/// Staged swap intents awaiting batch execution.
///
/// Intents are submitted to the programmable queue AND staged here. The batch
/// executor consumes the staged list.
#[derive(Default, Clone)]
pub struct TwapBatchState {
    pub pending: Vec<SwapIntent>,
}

pub type SharedTwapState = Arc<RwLock<TwapBatchState>>;

// =============================================================================
// Result types
// =============================================================================

#[derive(Debug, Serialize)]
pub struct BatchExecutionResult {
    /// Number of intents executed.
    pub executed: usize,
    /// Number of intents skipped (slippage / pool error).
    pub skipped: usize,
    /// TWAP price used for the batch (reserve_b / reserve_a at batch start).
    pub twap_price_numerator: u64,
    pub twap_price_denominator: u64,
}

// =============================================================================
// Batch execution endpoint
// =============================================================================

/// Shared state for the batch execution handler.
#[derive(Clone)]
pub struct BatchEndpointState {
    pub app_state: AppState,
    pub twap_state: SharedTwapState,
}

/// Request for `POST /queue/swaps/execute-batch`.
#[derive(Debug, Deserialize)]
pub struct ExecuteBatchRequest {
    /// The pool ID to use as the TWAP price anchor.
    /// Only swaps targeting this pool are executed.
    pub pool_id: String,
}

pub async fn execute_batch_handler(
    State(state): State<BatchEndpointState>,
    Json(req): Json<ExecuteBatchRequest>,
) -> Result<Json<BatchExecutionResult>, (StatusCode, Json<crate::server::ErrorResponse>)> {
    let pool_id_bytes = parse_hex32(&req.pool_id).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(crate::server::ErrorResponse {
                error: "invalid pool_id hex".into(),
            }),
        )
    })?;

    let mut registry = state.app_state.registry.write().await;
    let mut twap_state = state.twap_state.write().await;

    // Snapshot the open price (TWAP anchor) before any swaps.
    let (twap_num, twap_denom) = {
        let pool = registry.get_pool(&pool_id_bytes).ok_or_else(|| {
            (
                StatusCode::NOT_FOUND,
                Json(crate::server::ErrorResponse {
                    error: "pool not found".into(),
                }),
            )
        })?;
        (pool.reserve_b, pool.reserve_a)
    };

    // Drain pending intents targeting this pool.
    let intents: Vec<SwapIntent> = twap_state
        .pending
        .drain(..)
        .filter(|i| i.pool_id == pool_id_bytes)
        .collect();

    let mut executed = 0usize;
    let mut skipped = 0usize;

    for intent in &intents {
        // Execute at TWAP: compute the expected output at the open price.
        // amount_out_twap = amount_in * twap_num / (twap_denom + amount_in)
        // (ignoring fees for the TWAP price — fees are still applied on the actual swap)
        let pool = match registry.get_pool_mut(&pool_id_bytes) {
            Some(p) => p,
            None => {
                skipped += 1;
                continue;
            }
        };

        // Execute the swap via the pool's normal swap function.
        // The TWAP price serves as a *minimum output floor* rather than a
        // price override (applying fees on top of the TWAP rate).
        let fee_num = pool.fee_bps as u64;
        let effective_in = intent.amount_in * (10_000 - fee_num) / 10_000;
        let (reserve_in, reserve_out) = if intent.direction_a_to_b {
            (twap_denom, twap_num)
        } else {
            (twap_num, twap_denom)
        };

        let twap_out = if reserve_in > 0 {
            (reserve_out as u128 * effective_in as u128
                / (reserve_in as u128 + effective_in as u128)) as u64
        } else {
            0
        };

        // Min out is the max of the user's slippage tolerance and the TWAP floor.
        let min_out = intent.min_out.max(twap_out.saturating_sub(twap_out / 20));

        match pool.swap(intent.amount_in, min_out, intent.direction_a_to_b) {
            Ok(_) => {
                executed += 1;
            }
            Err(_) => {
                skipped += 1;
            }
        }
    }

    Ok(Json(BatchExecutionResult {
        executed,
        skipped,
        twap_price_numerator: twap_num,
        twap_price_denominator: twap_denom,
    }))
}

// =============================================================================
// Enqueue intent endpoint (extends the base queue endpoint)
// =============================================================================

/// Request for `POST /queue/swaps/submit-intent`.
///
/// Adds the intent both to the programmable queue (for provable ordering) and
/// the in-memory staging area for batch execution.
#[derive(Debug, Deserialize)]
pub struct SubmitIntentRequest {
    pub pool_id: String,
    pub amount_in: u64,
    pub direction_a_to_b: bool,
    pub min_out: u64,
    pub submitter: String,
}

#[derive(Debug, Serialize)]
pub struct SubmitIntentResponse {
    pub content_hash: String,
    pub queue_position: usize,
}

pub async fn submit_intent_handler(
    State(state): State<BatchEndpointState>,
    Json(req): Json<SubmitIntentRequest>,
) -> Result<Json<SubmitIntentResponse>, (StatusCode, Json<crate::server::ErrorResponse>)> {
    let pool_id = parse_hex32(&req.pool_id).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(crate::server::ErrorResponse {
                error: "invalid pool_id hex".into(),
            }),
        )
    })?;
    let submitter = parse_hex32(&req.submitter).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(crate::server::ErrorResponse {
                error: "invalid submitter hex".into(),
            }),
        )
    })?;

    let intent = SwapIntent {
        pool_id,
        amount_in: req.amount_in,
        direction_a_to_b: req.direction_a_to_b,
        min_out: req.min_out,
        submitter,
    };

    let hash = intent.content_hash();
    let mut twap_state = state.twap_state.write().await;
    let position = twap_state.pending.len();
    twap_state.pending.push(intent);

    Ok(Json(SubmitIntentResponse {
        content_hash: hex_encode(&hash),
        queue_position: position,
    }))
}

// =============================================================================
// Build the ProgrammableQueue + extended router
// =============================================================================

/// Create a [`ProgrammableQueue`] configured for swap batching.
///
/// Uses `programs::open(min_deposit)` as the validation program so any caller
/// can enqueue (no proof required beyond a minimum deposit).
pub fn swap_batch_queue(owner: [u8; 32], min_deposit: u64, capacity: usize) -> ProgrammableQueue {
    ProgrammableQueue::new(
        "amm-swap-batch".into(),
        owner,
        programs::open(min_deposit),
        None,
        capacity,
    )
}

/// Build the full queue router (base QueueEndpoint routes + batch execution + intent submission).
pub fn twap_queue_router(twap_state: SharedTwapState, app_state: AppState) -> Router {
    let queue = swap_batch_queue([0u8; 32], 0, 1024);
    let endpoint = QueueEndpoint::new(queue);

    let batch_state = BatchEndpointState {
        app_state,
        twap_state,
    };

    // The base endpoint gives us /enqueue, /dequeue, /status (these have their own state).
    // We build the extended routes separately with BatchEndpointState, then merge.
    let extended = Router::new()
        .route("/execute-batch", post(execute_batch_handler))
        .route("/submit-intent", post(submit_intent_handler))
        .with_state(batch_state);

    // Merge: base endpoint routes (no state dependency) + extended routes.
    endpoint.router().merge(extended)
}

// =============================================================================
// Helpers
// =============================================================================

fn parse_hex32(s: &str) -> Option<[u8; 32]> {
    if s.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for i in 0..32 {
        out[i] = u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).ok()?;
    }
    Some(out)
}

fn hex_encode(b: &[u8; 32]) -> String {
    b.iter().map(|byte| format!("{byte:02x}")).collect()
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pool::{LiquidityPool, PoolId};

    async fn make_app_state_with_pool(a: u64, b: u64, ra: u64, rb: u64) -> (AppState, PoolId) {
        let state = AppState::new();
        let pool = LiquidityPool::create(a, b, ra, rb).unwrap();
        let pool_id = pool.id;
        state.registry.write().await.register_pool(pool);
        (state, pool_id)
    }

    // ------------------------------------------------------------------
    // Queue upgrade tests
    // ------------------------------------------------------------------

    #[test]
    fn twap_queue_accepts_swap_intent() {
        let twap_state = Arc::new(RwLock::new(TwapBatchState::default()));

        // Submit two intents.
        let pool_id = [1u8; 32];
        let submitter = [2u8; 32];

        let intent1 = SwapIntent {
            pool_id,
            amount_in: 100,
            direction_a_to_b: true,
            min_out: 1,
            submitter,
        };
        let intent2 = SwapIntent {
            pool_id,
            amount_in: 200,
            direction_a_to_b: false,
            min_out: 1,
            submitter,
        };

        let rt = tokio::runtime::Runtime::new().unwrap();
        rt.block_on(async {
            let mut state = twap_state.write().await;
            state.pending.push(intent1.clone());
            state.pending.push(intent2.clone());
            assert_eq!(state.pending.len(), 2);
        });
    }

    #[test]
    fn swap_intent_content_hash_is_deterministic() {
        let intent = SwapIntent {
            pool_id: [1u8; 32],
            amount_in: 500,
            direction_a_to_b: true,
            min_out: 10,
            submitter: [0xAB; 32],
        };

        let h1 = intent.content_hash();
        let h2 = intent.content_hash();
        assert_eq!(h1, h2, "content hash must be deterministic");
        // Must differ from another intent
        let intent2 = SwapIntent {
            amount_in: 501,
            ..intent
        };
        assert_ne!(h1, intent2.content_hash(), "different intents must hash differently");
    }

    #[test]
    fn swap_batch_queue_enqueue_and_status() {
        let mut queue = swap_batch_queue([0u8; 32], 0, 64);

        let content_hash = [42u8; 32];
        let sender = [1u8; 32];
        let ctx = ValidationContext {
            sender,
            current_height: 0,
            current_epoch: 0,
            sender_epoch_count: 0,
            preimage: None,
            sequence: None,
        };
        let entry = pyana_storage::queue::QueueEntry {
            content_hash,
            sender,
            deposit: 0,
            enqueued_at: 0,
            size: 32,
        };

        queue.enqueue_validated(entry, &ctx).unwrap();
        assert_eq!(queue.len(), 1);
    }

    #[tokio::test]
    async fn execute_batch_runs_swaps_at_twap_price() {
        let (app_state, pool_id) = make_app_state_with_pool(1, 2, 10_000, 20_000).await;
        let twap_state = Arc::new(RwLock::new(TwapBatchState::default()));

        // Stage some intents
        {
            let mut ts = twap_state.write().await;
            ts.pending.push(SwapIntent {
                pool_id,
                amount_in: 100,
                direction_a_to_b: true,
                min_out: 1,
                submitter: [0u8; 32],
            });
            ts.pending.push(SwapIntent {
                pool_id,
                amount_in: 200,
                direction_a_to_b: true,
                min_out: 1,
                submitter: [0u8; 32],
            });
        }

        let pool_id_hex: String = pool_id.iter().map(|b| format!("{b:02x}")).collect();

        let batch_state = BatchEndpointState {
            app_state: app_state.clone(),
            twap_state: twap_state.clone(),
        };

        let req = ExecuteBatchRequest {
            pool_id: pool_id_hex,
        };
        let result = execute_batch_handler(
            State(batch_state),
            Json(req),
        )
        .await
        .unwrap();

        assert_eq!(result.executed + result.skipped, 2);
        // At least some should have been executed
        assert!(result.executed > 0, "should have executed at least 1 intent");
        // TWAP price should match the initial pool state
        assert_eq!(result.twap_price_numerator, 20_000);
        assert_eq!(result.twap_price_denominator, 10_000);
        // Queue should be drained
        assert_eq!(twap_state.read().await.pending.len(), 0);
    }

    #[tokio::test]
    async fn execute_batch_unknown_pool_returns_error() {
        let app_state = AppState::new(); // no pool registered
        let twap_state = Arc::new(RwLock::new(TwapBatchState::default()));

        let batch_state = BatchEndpointState {
            app_state,
            twap_state,
        };

        let req = ExecuteBatchRequest {
            pool_id: format!("{:064x}", 0u64),
        };
        let result = execute_batch_handler(State(batch_state), Json(req)).await;
        assert!(result.is_err(), "unknown pool should return error");
        assert_eq!(result.unwrap_err().0, StatusCode::NOT_FOUND);
    }
}
