//! Minimal HTTP API server for the orderbook exchange.

use std::sync::Arc;

use axum::{
    Json, Router,
    extract::{Path, State},
    http::StatusCode,
    routing::{delete, get, post},
};
use serde::{Deserialize, Serialize};
use tokio::sync::RwLock;

use crate::OrderbookEngine;
use crate::book::TradingPair;
use crate::order::{Order, OrderId, OrderStatus, OrderType, Side, TimeInForce};

// =============================================================================
// Application State
// =============================================================================

#[derive(Clone)]
pub struct AppState {
    pub engine: Arc<RwLock<OrderbookEngine>>,
    pub trades: Arc<RwLock<Vec<TradeRecord>>>,
}

#[derive(Clone, Serialize)]
pub struct TradeRecord {
    pub buyer_order_id: String,
    pub seller_order_id: String,
    pub price: u64,
    pub amount: u64,
    pub timestamp: u64,
}

impl AppState {
    pub fn new() -> Self {
        let pair = TradingPair {
            base: "ETH".to_string(),
            quote: "USDC".to_string(),
        };
        Self {
            engine: Arc::new(RwLock::new(OrderbookEngine::new(pair))),
            trades: Arc::new(RwLock::new(Vec::new())),
        }
    }
}

// =============================================================================
// Request/Response Types
// =============================================================================

#[derive(Deserialize)]
pub struct SubmitOrderRequest {
    pub side: String,
    pub order_type: String,
    pub price: Option<u64>,
    pub amount: u64,
    pub time_in_force: Option<String>,
}

#[derive(Serialize)]
pub struct OrderResponse {
    pub id: String,
    pub side: String,
    pub order_type: String,
    pub price: Option<u64>,
    pub remaining_amount: u64,
    pub status: String,
    pub created_at: u64,
}

#[derive(Serialize)]
pub struct BookSnapshot {
    pub pair: String,
    pub bids: Vec<LevelResponse>,
    pub asks: Vec<LevelResponse>,
}

#[derive(Serialize)]
pub struct LevelResponse {
    pub price: u64,
    pub quantity: u64,
    pub num_orders: usize,
}

#[derive(Serialize)]
pub struct MatchResponse {
    pub fills: usize,
    pub message: String,
}

#[derive(Serialize)]
pub struct ErrorResponse {
    pub error: String,
}

// =============================================================================
// Router
// =============================================================================

pub fn router() -> Router<AppState> {
    Router::new()
        .route("/orders", post(submit_order))
        .route("/orders/{id}", get(get_order))
        .route("/orders/{id}", delete(cancel_order))
        .route("/book/{pair}", get(get_book))
        .route("/match", post(trigger_match))
        .route("/trades", get(get_trades))
        .route("/health", get(health_check))
}

// =============================================================================
// Helpers
// =============================================================================

fn hex_id(id: &[u8; 32]) -> String {
    id.iter().map(|b| format!("{b:02x}")).collect()
}

fn parse_hex_id(s: &str) -> Option<[u8; 32]> {
    if s.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for i in 0..32 {
        out[i] = u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).ok()?;
    }
    Some(out)
}

fn order_to_response(order: &Order) -> OrderResponse {
    OrderResponse {
        id: hex_id(&order.id),
        side: match order.side() {
            Side::Buy => "buy".to_string(),
            Side::Sell => "sell".to_string(),
        },
        order_type: match &order.order_type {
            OrderType::Limit { .. } => "limit".to_string(),
            OrderType::Market { .. } => "market".to_string(),
            OrderType::StopLoss { .. } => "stop_loss".to_string(),
        },
        price: order.price(),
        remaining_amount: order.remaining_amount,
        status: match &order.status {
            OrderStatus::Open => "open".to_string(),
            OrderStatus::PartiallyFilled { filled_amount } => {
                format!("partial_{filled_amount}")
            }
            OrderStatus::Filled => "filled".to_string(),
            OrderStatus::Cancelled => "cancelled".to_string(),
            OrderStatus::Expired => "expired".to_string(),
            OrderStatus::Pending => "pending".to_string(),
        },
        created_at: order.created_at,
    }
}

// =============================================================================
// Handlers
// =============================================================================

async fn submit_order(
    State(state): State<AppState>,
    Json(req): Json<SubmitOrderRequest>,
) -> Result<(StatusCode, Json<OrderResponse>), (StatusCode, Json<ErrorResponse>)> {
    let side = match req.side.as_str() {
        "buy" => Side::Buy,
        "sell" => Side::Sell,
        _ => {
            return Err((
                StatusCode::BAD_REQUEST,
                Json(ErrorResponse {
                    error: "side must be 'buy' or 'sell'".to_string(),
                }),
            ));
        }
    };

    let tif = match req.time_in_force.as_deref() {
        Some("ioc") | Some("IOC") => TimeInForce::IOC,
        Some("fok") | Some("FOK") => TimeInForce::FOK,
        _ => TimeInForce::GTC,
    };

    let order_type = match req.order_type.as_str() {
        "limit" => {
            let price = req.price.ok_or_else(|| {
                (
                    StatusCode::BAD_REQUEST,
                    Json(ErrorResponse {
                        error: "limit order requires price".to_string(),
                    }),
                )
            })?;
            OrderType::Limit {
                price,
                amount: req.amount,
                side,
                time_in_force: tif,
            }
        }
        "market" => OrderType::Market {
            amount: req.amount,
            side,
            slippage_bps: 500,
        },
        _ => {
            return Err((
                StatusCode::BAD_REQUEST,
                Json(ErrorResponse {
                    error: "order_type must be 'limit' or 'market'".to_string(),
                }),
            ));
        }
    };

    let trader = pyana_types::CellId([0xAA; 32]);
    let mut engine = state.engine.write().await;
    let height = engine.current_height;
    let nonce = engine.sequence;

    let order = Order::new(trader, order_type, nonce, height);
    let resp = order_to_response(&order);

    // Use unverified path (no escrow required for devnet).
    let match_result = engine.submit_order_unverified(order).map_err(|e| {
        (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(ErrorResponse {
                error: format!("match error: {e}"),
            }),
        )
    })?;

    // Record fills as trades.
    if !match_result.fills.is_empty() {
        let mut trades = state.trades.write().await;
        for fill in &match_result.fills {
            trades.push(TradeRecord {
                buyer_order_id: hex_id(&fill.taker_order_id),
                seller_order_id: hex_id(&fill.maker_order_id),
                price: fill.price,
                amount: fill.amount,
                timestamp: height,
            });
        }
    }

    Ok((StatusCode::CREATED, Json(resp)))
}

async fn get_order(
    State(state): State<AppState>,
    Path(id): Path<String>,
) -> Result<Json<OrderResponse>, (StatusCode, Json<ErrorResponse>)> {
    let id_bytes = parse_hex_id(&id).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid id format".to_string(),
            }),
        )
    })?;

    let engine = state.engine.read().await;
    let order = engine.book.get_order(&id_bytes).ok_or_else(|| {
        (
            StatusCode::NOT_FOUND,
            Json(ErrorResponse {
                error: "order not found".to_string(),
            }),
        )
    })?;

    Ok(Json(order_to_response(order)))
}

async fn cancel_order(
    State(state): State<AppState>,
    Path(id): Path<String>,
) -> Result<Json<OrderResponse>, (StatusCode, Json<ErrorResponse>)> {
    let id_bytes = parse_hex_id(&id).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid id format".to_string(),
            }),
        )
    })?;

    let mut engine = state.engine.write().await;
    let order = engine.book.remove_order(&id_bytes).ok_or_else(|| {
        (
            StatusCode::NOT_FOUND,
            Json(ErrorResponse {
                error: "order not found".to_string(),
            }),
        )
    })?;

    let mut cancelled = order;
    cancelled.status = OrderStatus::Cancelled;
    Ok(Json(order_to_response(&cancelled)))
}

async fn get_book(State(state): State<AppState>, Path(_pair): Path<String>) -> Json<BookSnapshot> {
    let engine = state.engine.read().await;

    let bids: Vec<LevelResponse> = engine
        .book
        .bid_levels()
        .map(|level| LevelResponse {
            price: level.price,
            quantity: level.total_quantity(),
            num_orders: level.orders.len(),
        })
        .collect();

    let asks: Vec<LevelResponse> = engine
        .book
        .ask_levels()
        .map(|level| LevelResponse {
            price: level.price,
            quantity: level.total_quantity(),
            num_orders: level.orders.len(),
        })
        .collect();

    let pair_str = format!("{}/{}", engine.book.pair.base, engine.book.pair.quote);
    Json(BookSnapshot {
        pair: pair_str,
        bids,
        asks,
    })
}

async fn trigger_match(State(state): State<AppState>) -> Json<MatchResponse> {
    let mut engine = state.engine.write().await;
    let results = engine.process_reveal_batch();
    let fills: usize = results
        .iter()
        .filter_map(|r| r.as_ref().ok())
        .map(|r| r.result.fills.len())
        .sum();

    Json(MatchResponse {
        fills,
        message: format!("processed {} reveal batch results", results.len()),
    })
}

async fn get_trades(State(state): State<AppState>) -> Json<Vec<TradeRecord>> {
    let trades = state.trades.read().await;
    Json(trades.clone())
}

async fn health_check() -> &'static str {
    "ok"
}
