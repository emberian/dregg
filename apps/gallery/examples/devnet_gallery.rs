//! Full devnet boot + gallery server + simulated bids.
//!
//! This example:
//! 1. Starts the gallery server in-process
//! 2. Registers artwork via the HTTP API
//! 3. Creates an auction
//! 4. Simulates two bidders placing bids (commit-reveal)
//! 5. Advances phases and triggers settlement
//! 6. Verifies the final state
//!
//! ## Running
//!
//! ```bash
//! cargo run -p pyana-gallery --example devnet_gallery
//! ```

use pyana_gallery::server::start_server;
use pyana_gallery::{
    CreateAuctionRequest, RegisterArtworkRequest, RevealBidRequest, SubmitBidRequest,
    compute_bid_commitment, id_to_hex,
};

use pyana_app_framework::CellId;
use pyana_app_framework::server::AppConfig;
use reqwest::Client;
use serde_json::Value;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt().init();

    println!("=== Pyana Gallery: Devnet Integration Demo ===\n");

    // =========================================================================
    // Step 0: Start gallery server
    // =========================================================================
    println!("[0] Starting gallery server...");

    let config = AppConfig::default().with_listen("127.0.0.1:0");

    let addr = start_server(config, None).await;
    let base = format!("http://{addr}");
    println!("    Gallery server at {base}");

    tokio::time::sleep(std::time::Duration::from_millis(50)).await;

    let client = Client::new();

    // Health check.
    let health: Value = client
        .get(format!("{base}/health"))
        .send()
        .await?
        .json()
        .await?;
    println!("    Status: {}", health["status"]);
    println!();

    // =========================================================================
    // Step 1: Set up participants
    // =========================================================================
    let artist = CellId::from_bytes([0xAA; 32]);
    let bidder_alice = CellId::from_bytes([0x01; 32]);
    let bidder_bob = CellId::from_bytes([0x02; 32]);

    let artist_hex = id_to_hex(artist.as_bytes());
    let alice_hex = id_to_hex(bidder_alice.as_bytes());
    let bob_hex = id_to_hex(bidder_bob.as_bytes());

    println!("[1] Participants:");
    println!("    Artist: {}...", &artist_hex[..16]);
    println!("    Alice:  {}...", &alice_hex[..16]);
    println!("    Bob:    {}...", &bob_hex[..16]);
    println!();

    // Advance height.
    let _: Value = client
        .post(format!("{base}/admin/height"))
        .json(&serde_json::json!({"delta": 10}))
        .send()
        .await?
        .json()
        .await?;

    // =========================================================================
    // Step 2: Register artwork
    // =========================================================================
    println!("[2] Registering artwork...");

    let image_hash = id_to_hex(blake3::hash(b"gallery-launch-piece").as_bytes());

    let register_req = RegisterArtworkRequest {
        title: "Moons' Gallery Launch".to_string(),
        description: "The inaugural piece for the moons' gallery launch event.".to_string(),
        image_hash: image_hash.clone(),
        artist_cell: artist_hex.clone(),
        reserve_price: 3000,
        tags: vec![
            "launch".to_string(),
            "inaugural".to_string(),
            "digital".to_string(),
        ],
    };

    let resp: Value = client
        .post(format!("{base}/artworks"))
        .json(&register_req)
        .send()
        .await?
        .json()
        .await?;

    let artwork_id = resp["id"].as_str().unwrap().to_string();
    println!("    Artwork ID: {artwork_id}");
    println!("    Status: {}", resp["status"]);
    println!();

    // =========================================================================
    // Step 3: Create auction
    // =========================================================================
    println!("[3] Creating auction...");

    let auction_req = CreateAuctionRequest {
        artwork_id: artwork_id.clone(),
        artist_cell: artist_hex.clone(),
        bidding_duration: 20,
        reveal_duration: 10,
    };

    let resp: Value = client
        .post(format!("{base}/auctions"))
        .json(&auction_req)
        .send()
        .await?
        .json()
        .await?;

    let auction_id = resp["id"].as_str().unwrap().to_string();
    println!("    Auction ID: {auction_id}");
    println!("    Phase: {}", resp["status"]);
    println!();

    // =========================================================================
    // Step 4: Place bids (commit phase)
    // =========================================================================
    println!("[4] Placing bid commitments...");

    let alice_nonce = *blake3::hash(b"alice-nonce-gallery").as_bytes();
    let bob_nonce = *blake3::hash(b"bob-nonce-gallery").as_bytes();
    let alice_amount = 5000u64;
    let bob_amount = 8500u64;

    let alice_commitment = compute_bid_commitment(&bidder_alice, alice_amount, &alice_nonce);
    let bob_commitment = compute_bid_commitment(&bidder_bob, bob_amount, &bob_nonce);

    // Alice bids.
    let bid_req = SubmitBidRequest {
        commitment: id_to_hex(&alice_commitment),
        bidder_cell: alice_hex.clone(),
        escrow_amount: alice_amount,
    };

    let resp: Value = client
        .post(format!("{base}/auctions/{auction_id}/bid"))
        .json(&bid_req)
        .send()
        .await?
        .json()
        .await?;
    println!(
        "    Alice bid: {} (commitment: {}...)",
        resp["status"],
        &id_to_hex(&alice_commitment)[..12]
    );

    // Bob bids.
    let bid_req = SubmitBidRequest {
        commitment: id_to_hex(&bob_commitment),
        bidder_cell: bob_hex.clone(),
        escrow_amount: bob_amount,
    };

    let resp: Value = client
        .post(format!("{base}/auctions/{auction_id}/bid"))
        .json(&bid_req)
        .send()
        .await?
        .json()
        .await?;
    println!(
        "    Bob bid: {} (commitment: {}...)",
        resp["status"],
        &id_to_hex(&bob_commitment)[..12]
    );
    println!();

    // =========================================================================
    // Step 5: Advance to reveal phase
    // =========================================================================
    println!("[5] Advancing to reveal phase...");

    let _: Value = client
        .post(format!("{base}/admin/height"))
        .json(&serde_json::json!({"delta": 21}))
        .send()
        .await?
        .json()
        .await?;
    println!("    Block height advanced past bidding deadline.");
    println!();

    // =========================================================================
    // Step 6: Reveal bids
    // =========================================================================
    println!("[6] Revealing bids...");

    let reveal_req = RevealBidRequest {
        commitment: id_to_hex(&alice_commitment),
        bidder_cell: alice_hex.clone(),
        amount: alice_amount,
        nonce: id_to_hex(&alice_nonce),
    };

    let resp: Value = client
        .post(format!("{base}/auctions/{auction_id}/reveal"))
        .json(&reveal_req)
        .send()
        .await?
        .json()
        .await?;
    println!(
        "    Alice revealed: {} units (status: {})",
        alice_amount, resp["status"]
    );

    let reveal_req = RevealBidRequest {
        commitment: id_to_hex(&bob_commitment),
        bidder_cell: bob_hex.clone(),
        amount: bob_amount,
        nonce: id_to_hex(&bob_nonce),
    };

    let resp: Value = client
        .post(format!("{base}/auctions/{auction_id}/reveal"))
        .json(&reveal_req)
        .send()
        .await?
        .json()
        .await?;
    println!(
        "    Bob revealed: {} units (status: {})",
        bob_amount, resp["status"]
    );
    println!();

    // =========================================================================
    // Step 7: Advance to settlement and trigger
    // =========================================================================
    println!("[7] Settling auction...");

    let _: Value = client
        .post(format!("{base}/admin/height"))
        .json(&serde_json::json!({"delta": 10}))
        .send()
        .await?
        .json()
        .await?;

    let resp: Value = client
        .post(format!("{base}/admin/settle/{auction_id}"))
        .send()
        .await?
        .json()
        .await?;
    println!("    Settlement status: {}", resp["status"]);
    println!();

    // =========================================================================
    // Step 8: Verify result
    // =========================================================================
    println!("[8] Verifying auction result...");

    let resp: Value = client
        .get(format!("{base}/auctions/{auction_id}/result"))
        .send()
        .await?
        .json()
        .await?;
    println!("    Status: {}", resp["status"]);
    println!("    Winner: {}", resp["winner"].as_str().unwrap_or("?"));
    println!("    Winning bid: {}", resp["winning_bid"]);
    println!(
        "    Receipt: {}",
        resp["receipt_hash"].as_str().unwrap_or("?")
    );
    println!();

    // =========================================================================
    // Step 9: Check provenance
    // =========================================================================
    println!("[9] Checking artwork provenance...");

    let resp: Value = client
        .get(format!("{base}/artworks/{artwork_id}"))
        .send()
        .await?
        .json()
        .await?;
    println!(
        "    Current owner: {}",
        resp["current_owner"].as_str().unwrap_or("?")
    );
    println!(
        "    Provenance entries: {}",
        resp["provenance"].as_array().map(|a| a.len()).unwrap_or(0)
    );

    if let Some(provenance) = resp["provenance"].as_array() {
        for (i, entry) in provenance.iter().enumerate() {
            println!(
                "      [{}] {} -> {} (price: {})",
                i,
                &entry["from"].as_str().unwrap_or("?")[..8],
                &entry["to"].as_str().unwrap_or("?")[..8],
                entry["price"]
            );
        }
    }
    println!();

    // =========================================================================
    // Summary
    // =========================================================================
    println!("=== Devnet Gallery Demo Complete ===\n");
    println!("Full stack exercised:");
    println!("  Gallery Server (axum) -> pyana-sdk (PyanaEngine) -> Turn execution");
    println!("  REST API -> Commit-Reveal Bidding -> Atomic Settlement -> Provenance");
    println!();
    println!("Server remains running at: {base}");
    println!("  GET  {base}/artworks");
    println!("  GET  {base}/auctions");
    println!("  GET  {base}/health");
    println!("  WS   ws://{addr}/ws (live updates)");

    Ok(())
}
