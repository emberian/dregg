//! HTTP handlers for the gallery API.
//!
//! All handlers are async functions that take Axum extractors and return JSON responses.
//! Admin endpoints are protected by the `AdminAuth` extractor from `pyana-app-framework`.

use axum::{
    Json,
    extract::{Path, State},
    http::StatusCode,
    response::IntoResponse,
};
use serde_json::json;
use tracing::{info, warn};

use pyana_app_framework::auth::AdminAuth;
use pyana_app_framework::authorizer::{Authorizer, SignedAuthorizer};
use pyana_app_framework::hex::hex_to_bytes32;
use pyana_app_framework::{CellId, EscrowCondition};

use crate::persistence::StateSnapshot;
use crate::server::AppState;
use crate::{
    CreateAuctionRequest, RegisterArtworkRequest, RevealBidRequest, SubmitBidRequest, WsEvent,
    id_from_hex, id_to_hex,
};

// =============================================================================
// Artwork Handlers
// =============================================================================

/// GET /artworks — List all artworks.
pub async fn list_artworks(State(state): State<AppState>) -> impl IntoResponse {
    let artworks = state.artwork_registry.list_all().await;
    Json(json!({
        "artworks": artworks,
        "count": artworks.len()
    }))
}

/// GET /artworks/:id — Get artwork details + provenance.
pub async fn get_artwork(
    State(state): State<AppState>,
    Path(id): Path<String>,
) -> impl IntoResponse {
    let artwork_id = match id_from_hex(&id) {
        Some(bytes) => bytes,
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid artwork ID hex"})),
            )
                .into_response();
        }
    };

    match state.artwork_registry.get(&artwork_id).await {
        Some(artwork) => {
            let provenance = state.provenance_registry.get_chain(&artwork_id).await;
            let provenance_json: Vec<_> = provenance
                .iter()
                .map(|p| {
                    json!({
                        "from": id_to_hex(p.from.as_bytes()),
                        "to": id_to_hex(p.to.as_bytes()),
                        "price": p.price,
                        "block_height": p.block_height,
                        "receipt_hash": id_to_hex(&p.receipt_hash),
                    })
                })
                .collect();

            Json(json!({
                "id": id_to_hex(&artwork.id),
                "title": artwork.title,
                "description": artwork.description,
                "image_hash": id_to_hex(&artwork.image_hash),
                "artist": id_to_hex(artwork.artist.as_bytes()),
                "current_owner": id_to_hex(artwork.current_owner.as_bytes()),
                "reserve_price": artwork.reserve_price,
                "registered_at": artwork.registered_at,
                "tags": artwork.tags,
                "provenance": provenance_json,
            }))
            .into_response()
        }
        None => (
            StatusCode::NOT_FOUND,
            Json(json!({"error": "artwork not found"})),
        )
            .into_response(),
    }
}

/// POST /artworks — Register a new artwork.
pub async fn register_artwork(
    State(state): State<AppState>,
    Json(req): Json<RegisterArtworkRequest>,
) -> impl IntoResponse {
    let artist = match hex_to_bytes32(&req.artist_cell) {
        Ok(bytes) => CellId::from_bytes(bytes),
        Err(_) => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid artist_cell hex"})),
            )
                .into_response();
        }
    };

    let image_hash = match hex_to_bytes32(&req.image_hash) {
        Ok(bytes) => bytes,
        Err(_) => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid image_hash hex"})),
            )
                .into_response();
        }
    };

    let current_height = state.auction_engine.current_height().await;

    let mut engine = state.engine.lock().await;
    match state
        .artwork_registry
        .register(
            &mut engine,
            req.title.clone(),
            req.description,
            image_hash,
            artist,
            req.reserve_price,
            req.tags,
            current_height,
        )
        .await
    {
        Ok(artwork_id) => {
            // Record provenance.
            state
                .provenance_registry
                .record_registration(artwork_id, artist, current_height)
                .await;

            // Broadcast event.
            state.ws_broadcaster.broadcast(WsEvent::NewArtwork {
                artwork_id: id_to_hex(&artwork_id),
                title: req.title,
                artist: id_to_hex(artist.as_bytes()),
            });

            info!(artwork_id = %id_to_hex(&artwork_id), "artwork registered");

            drop(engine);
            persist_state_background(&state).await;

            (
                StatusCode::CREATED,
                Json(json!({
                    "id": id_to_hex(&artwork_id),
                    "status": "registered"
                })),
            )
                .into_response()
        }
        Err(e) => {
            warn!(error = %e, "artwork registration failed");
            (StatusCode::CONFLICT, Json(json!({"error": e.to_string()}))).into_response()
        }
    }
}

// =============================================================================
// Auction Handlers
// =============================================================================

/// GET /auctions — List active auctions.
pub async fn list_auctions(State(state): State<AppState>) -> impl IntoResponse {
    let auctions = state.auction_engine.list_active().await;
    Json(json!({
        "auctions": auctions,
        "count": auctions.len()
    }))
}

/// GET /auctions/:id — Get auction details.
pub async fn get_auction(
    State(state): State<AppState>,
    Path(id): Path<String>,
) -> impl IntoResponse {
    let auction_id = match id_from_hex(&id) {
        Some(bytes) => bytes,
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid auction ID hex"})),
            )
                .into_response();
        }
    };

    match state.auction_engine.get(&auction_id).await {
        Some(auction) => {
            let response = state.auction_engine.auction_to_response(&auction);

            // Include bid history (commitments visible, amounts hidden until reveal).
            let commitments: Vec<_> = auction
                .commitments
                .iter()
                .map(|c| {
                    json!({
                        "commitment": id_to_hex(&c.commitment),
                        "bidder": id_to_hex(c.bidder.as_bytes()),
                        "submitted_at": c.submitted_at,
                    })
                })
                .collect();

            let revealed: Vec<_> = auction
                .revealed_bids
                .iter()
                .map(|r| {
                    json!({
                        "bidder": id_to_hex(r.bidder.as_bytes()),
                        "amount": r.amount,
                        "commitment": id_to_hex(&r.commitment),
                    })
                })
                .collect();

            Json(json!({
                "auction": response,
                "commitments": commitments,
                "revealed_bids": revealed,
            }))
            .into_response()
        }
        None => (
            StatusCode::NOT_FOUND,
            Json(json!({"error": "auction not found"})),
        )
            .into_response(),
    }
}

/// POST /auctions — Create a new auction.
pub async fn create_auction(
    State(state): State<AppState>,
    Json(req): Json<CreateAuctionRequest>,
) -> impl IntoResponse {
    let artwork_id = match id_from_hex(&req.artwork_id) {
        Some(bytes) => bytes,
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid artwork_id hex"})),
            )
                .into_response();
        }
    };

    let artist = match hex_to_bytes32(&req.artist_cell) {
        Ok(bytes) => CellId::from_bytes(bytes),
        Err(_) => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid artist_cell hex"})),
            )
                .into_response();
        }
    };

    // Verify artwork exists and caller is owner.
    let artwork = match state.artwork_registry.get(&artwork_id).await {
        Some(a) => a,
        None => {
            return (
                StatusCode::NOT_FOUND,
                Json(json!({"error": "artwork not found"})),
            )
                .into_response();
        }
    };

    if artwork.current_owner.as_bytes() != artist.as_bytes() {
        return (
            StatusCode::FORBIDDEN,
            Json(json!({"error": "only the current owner can create an auction"})),
        )
            .into_response();
    }

    match state
        .auction_engine
        .create_auction(
            artwork_id,
            artist,
            artwork.reserve_price,
            req.bidding_duration,
            req.reveal_duration,
        )
        .await
    {
        Ok(auction_id) => {
            state.ws_broadcaster.broadcast(WsEvent::PhaseChange {
                auction_id: id_to_hex(&auction_id),
                new_phase: "bidding".to_string(),
            });

            info!(auction_id = %id_to_hex(&auction_id), "auction created");

            persist_state_background(&state).await;

            (
                StatusCode::CREATED,
                Json(json!({
                    "id": id_to_hex(&auction_id),
                    "status": "bidding"
                })),
            )
                .into_response()
        }
        Err(e) => {
            warn!(error = %e, "auction creation failed");
            (StatusCode::CONFLICT, Json(json!({"error": e.to_string()}))).into_response()
        }
    }
}

/// POST /auctions/:id/bid — Submit a bid commitment.
pub async fn submit_bid(
    State(state): State<AppState>,
    Path(id): Path<String>,
    Json(req): Json<SubmitBidRequest>,
) -> impl IntoResponse {
    let auction_id = match id_from_hex(&id) {
        Some(bytes) => bytes,
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid auction ID hex"})),
            )
                .into_response();
        }
    };

    let commitment = match id_from_hex(&req.commitment) {
        Some(bytes) => bytes,
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid commitment hex"})),
            )
                .into_response();
        }
    };

    let bidder = match hex_to_bytes32(&req.bidder_cell) {
        Ok(bytes) => CellId::from_bytes(bytes),
        Err(_) => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid bidder_cell hex"})),
            )
                .into_response();
        }
    };

    // Create escrow for the bid amount.
    let auction = match state.auction_engine.get(&auction_id).await {
        Some(a) => a,
        None => {
            return (
                StatusCode::NOT_FOUND,
                Json(json!({"error": "auction not found"})),
            )
                .into_response();
        }
    };

    let escrow_condition = EscrowCondition::ProofPresented {
        verification_key: auction_id,
    };

    let mut engine = state.engine.lock().await;
    let mut mgr =
        pyana_app_framework::escrow::EscrowManager::new(&mut engine, make_escrow_authorizer());
    let escrow_id = match mgr.create_payment_escrow(
        bidder,
        auction.artist,
        req.escrow_amount,
        escrow_condition,
        auction.reveal_end_height,
    ) {
        Ok(id) => id,
        Err(e) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(json!({"error": format!("escrow creation failed: {e}")})),
            )
                .into_response();
        }
    };
    drop(engine);

    // Submit the bid commitment.
    match state
        .auction_engine
        .submit_bid(&auction_id, commitment, bidder, escrow_id)
        .await
    {
        Ok(()) => {
            state.ws_broadcaster.broadcast(WsEvent::NewBid {
                auction_id: id_to_hex(&auction_id),
                bidder: id_to_hex(bidder.as_bytes()),
                commitment: id_to_hex(&commitment),
            });

            info!(
                auction_id = %id_to_hex(&auction_id),
                bidder = %id_to_hex(bidder.as_bytes()),
                "bid committed"
            );

            persist_state_background(&state).await;

            (
                StatusCode::OK,
                Json(json!({
                    "status": "committed",
                    "escrow_id": id_to_hex(&escrow_id),
                })),
            )
                .into_response()
        }
        Err(e) => {
            warn!(error = %e, "bid submission failed");
            (StatusCode::CONFLICT, Json(json!({"error": e.to_string()}))).into_response()
        }
    }
}

/// POST /auctions/:id/reveal — Reveal a bid.
pub async fn reveal_bid(
    State(state): State<AppState>,
    Path(id): Path<String>,
    Json(req): Json<RevealBidRequest>,
) -> impl IntoResponse {
    let auction_id = match id_from_hex(&id) {
        Some(bytes) => bytes,
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid auction ID hex"})),
            )
                .into_response();
        }
    };

    let commitment = match id_from_hex(&req.commitment) {
        Some(bytes) => bytes,
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid commitment hex"})),
            )
                .into_response();
        }
    };

    let bidder = match hex_to_bytes32(&req.bidder_cell) {
        Ok(bytes) => CellId::from_bytes(bytes),
        Err(_) => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid bidder_cell hex"})),
            )
                .into_response();
        }
    };

    let nonce = match id_from_hex(&req.nonce) {
        Some(bytes) => bytes,
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid nonce hex"})),
            )
                .into_response();
        }
    };

    match state
        .auction_engine
        .reveal_bid(&auction_id, commitment, bidder, req.amount, nonce)
        .await
    {
        Ok(()) => {
            state.ws_broadcaster.broadcast(WsEvent::BidRevealed {
                auction_id: id_to_hex(&auction_id),
                bidder: id_to_hex(bidder.as_bytes()),
                amount: req.amount,
            });

            info!(
                auction_id = %id_to_hex(&auction_id),
                bidder = %id_to_hex(bidder.as_bytes()),
                amount = req.amount,
                "bid revealed"
            );

            persist_state_background(&state).await;

            (
                StatusCode::OK,
                Json(json!({
                    "status": "revealed",
                    "amount": req.amount,
                })),
            )
                .into_response()
        }
        Err(e) => {
            warn!(error = %e, "bid reveal failed");
            (StatusCode::CONFLICT, Json(json!({"error": e.to_string()}))).into_response()
        }
    }
}

/// GET /auctions/:id/result — Get settlement result.
pub async fn get_auction_result(
    State(state): State<AppState>,
    Path(id): Path<String>,
) -> impl IntoResponse {
    let auction_id = match id_from_hex(&id) {
        Some(bytes) => bytes,
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid auction ID hex"})),
            )
                .into_response();
        }
    };

    match state.auction_engine.get(&auction_id).await {
        Some(auction) => match &auction.phase {
            crate::AuctionPhase::Settled {
                winner,
                winning_bid,
                receipt_hash,
            } => Json(json!({
                "status": "settled",
                "winner": id_to_hex(winner.as_bytes()),
                "winning_bid": winning_bid,
                "receipt_hash": id_to_hex(receipt_hash),
            }))
            .into_response(),
            crate::AuctionPhase::NoBids => Json(json!({
                "status": "no_bids",
                "message": "auction ended with no valid bids"
            }))
            .into_response(),
            _ => Json(json!({
                "status": "pending",
                "phase": crate::phase_label(&auction.phase),
                "message": "auction has not settled yet"
            }))
            .into_response(),
        },
        None => (
            StatusCode::NOT_FOUND,
            Json(json!({"error": "auction not found"})),
        )
            .into_response(),
    }
}

// =============================================================================
// Admin Handlers (protected by AdminAuth extractor from pyana-app-framework)
// =============================================================================

/// POST /admin/height — Advance block height (devnet utility).
/// Protected by AdminAuth extractor (reads PYANA_ADMIN_TOKEN from state).
pub async fn advance_height(
    _auth: AdminAuth,
    State(state): State<AppState>,
    Json(body): Json<serde_json::Value>,
) -> impl IntoResponse {
    let delta = body["delta"].as_u64().unwrap_or(1);
    state.auction_engine.advance_height(delta).await;
    let new_height = state.auction_engine.current_height().await;
    Json(json!({"height": new_height})).into_response()
}

/// POST /admin/settle/:id — Trigger settlement for an auction.
/// Protected by AdminAuth extractor (reads PYANA_ADMIN_TOKEN from state).
pub async fn trigger_settle(
    _auth: AdminAuth,
    State(state): State<AppState>,
    Path(id): Path<String>,
) -> impl IntoResponse {
    let auction_id = match id_from_hex(&id) {
        Some(bytes) => bytes,
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid auction ID hex"})),
            )
                .into_response();
        }
    };

    // First try to advance the phase.
    state.auction_engine.advance_phase(&auction_id).await;

    let mut engine = state.engine.lock().await;
    match state.auction_engine.settle(&auction_id, &mut engine).await {
        Ok(phase) => {
            if let crate::AuctionPhase::Settled {
                winner,
                winning_bid,
                receipt_hash,
            } = &phase
            {
                // Update artwork ownership.
                let auction = state.auction_engine.get(&auction_id).await.unwrap();
                state
                    .artwork_registry
                    .transfer_ownership(&auction.artwork_id, *winner)
                    .await;

                // Record provenance.
                let current_height = state.auction_engine.current_height().await;
                state
                    .provenance_registry
                    .record_transfer(
                        &auction.artwork_id,
                        auction.artist,
                        *winner,
                        *winning_bid,
                        current_height,
                        *receipt_hash,
                    )
                    .await;

                // Broadcast settlement event.
                state.ws_broadcaster.broadcast(WsEvent::AuctionSettled {
                    auction_id: id_to_hex(&auction_id),
                    winner: id_to_hex(winner.as_bytes()),
                    winning_bid: *winning_bid,
                });

                info!(
                    auction_id = %id_to_hex(&auction_id),
                    winner = %id_to_hex(winner.as_bytes()),
                    winning_bid,
                    "auction settled"
                );
            }

            drop(engine);
            persist_state_background(&state).await;

            Json(json!({
                "status": crate::phase_label(&phase),
            }))
            .into_response()
        }
        Err(e) => {
            warn!(error = %e, "settlement failed");
            (StatusCode::CONFLICT, Json(json!({"error": e.to_string()}))).into_response()
        }
    }
}

/// POST /admin/persist — Force persist state to disk.
/// Protected by AdminAuth extractor (reads PYANA_ADMIN_TOKEN from state).
pub async fn persist_state(_auth: AdminAuth, State(state): State<AppState>) -> impl IntoResponse {
    match do_persist(&state).await {
        Ok(path) => Json(json!({"status": "persisted", "path": path})).into_response(),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(json!({"error": format!("persistence failed: {e}")})),
        )
            .into_response(),
    }
}

/// GET /health — Health check.
pub async fn health_check(State(state): State<AppState>) -> impl IntoResponse {
    let height = state.auction_engine.current_height().await;
    let artworks = state.artwork_registry.list_all().await;
    let auctions = state.auction_engine.list_all().await;

    let active_auctions = auctions
        .iter()
        .filter(|a| a.phase == "bidding" || a.phase == "reveal")
        .count();
    let settled_auctions = auctions.iter().filter(|a| a.phase == "settled").count();

    Json(json!({
        "status": "running",
        "service": "pyana-gallery",
        "block_height": height,
        "artworks": {
            "total": artworks.len(),
        },
        "auctions": {
            "total": auctions.len(),
            "active": active_auctions,
            "settled": settled_auctions,
        }
    }))
}

// =============================================================================
// Persistence Helpers
// =============================================================================

/// Persist state in the background (non-blocking, best-effort).
async fn persist_state_background(state: &AppState) {
    if let Err(e) = do_persist(state).await {
        tracing::warn!(error = %e, "background state persistence failed");
    }
}

/// Actually persist state to disk using the framework's `JsonPersistence`.
async fn do_persist(state: &AppState) -> Result<String, String> {
    let persist = match &state.persistence {
        Some(p) => p,
        None => return Err("no persistence configured".to_string()),
    };

    let snapshot = StateSnapshot::capture(
        &state.artwork_registry,
        &state.auction_engine,
        &state.provenance_registry,
    )
    .await;

    persist.save(&snapshot).map_err(|e| e.to_string())?;
    Ok(persist.path().display().to_string())
}

/// Build the default `Authorizer` used by the gallery's escrow turns.
///
/// Reads `PYANA_GALLERY_ESCROW_KEY` (32-byte hex) from the environment when set;
/// otherwise falls back to a deterministic dev-only key and emits a warning.
/// Production deployments MUST set `PYANA_GALLERY_ESCROW_KEY`.
fn make_escrow_authorizer() -> Box<dyn Authorizer> {
    let secret = match std::env::var("PYANA_GALLERY_ESCROW_KEY") {
        Ok(hex) => parse_hex_32(&hex).unwrap_or_else(|| {
            eprintln!(
                "WARNING: PYANA_GALLERY_ESCROW_KEY is not valid 32-byte hex; using dev key"
            );
            dev_key_bytes()
        }),
        Err(_) => {
            eprintln!(
                "WARNING: PYANA_GALLERY_ESCROW_KEY not set; using deterministic dev key. \
                 DO NOT use this in production."
            );
            dev_key_bytes()
        }
    };
    Box::new(SignedAuthorizer::from_secret_bytes(secret))
}

fn dev_key_bytes() -> [u8; 32] {
    *blake3::hash(b"pyana-gallery-dev-escrow-key-v1").as_bytes()
}

fn parse_hex_32(s: &str) -> Option<[u8; 32]> {
    let s = s.trim().trim_start_matches("0x");
    if s.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for i in 0..32 {
        out[i] = u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).ok()?;
    }
    Some(out)
}
