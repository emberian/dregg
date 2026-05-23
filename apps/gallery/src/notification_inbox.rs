//! Store-and-forward inbox for auction notifications.
//!
//! This module wraps [`InboxEndpoint`] to provide a bidder notification inbox at
//! `/inbox/bidders/*`.  When a bidder is outbid or wins, the auction logic pushes
//! an [`InboxMessage::Encrypted`] to their inbox.  Bidders can retrieve messages
//! even after coming back online from an extended absence.
//!
//! # Route summary
//!
//! | Method | Path | Description |
//! |--------|------|-------------|
//! | POST | `/inbox/bidders/send` | Push a notification to the inbox |
//! | GET  | `/inbox/bidders/next` | Read the next queued notification |
//! | GET  | `/inbox/bidders/status` | Inbox status (pending count, etc.) |
//!
//! # Message conventions
//!
//! Notifications use `InboxMessage::Encrypted { ciphertext, sender }` so that
//! the gallery operator cannot read the message content (the bidder's client-side
//! key decrypts it).
//!
//! Two lifecycle events generate notifications:
//!
//! - **Outbid**: `"outbid:<auction_id>:<new_high_bid_hex>"` (encrypted with bidder pubkey).
//! - **Won**: `"won:<auction_id>:claim_within_50_blocks"` (encrypted with winner pubkey).

use pyana_app_framework::inbox_endpoint::InboxEndpoint;

/// Default inbox capacity per auction window.
pub const INBOX_CAPACITY: usize = 512;

/// Minimum deposit required to post a notification (anti-spam).
pub const INBOX_MIN_DEPOSIT: u64 = 0;

/// Build a fresh [`InboxEndpoint`] for the bidder notification inbox.
///
/// The gallery server mounts this at `/inbox/bidders` via
/// `AppServer::with_inbox("/inbox/bidders", bidder_inbox_endpoint())`.
pub fn bidder_inbox_endpoint() -> InboxEndpoint {
    InboxEndpoint::new(INBOX_CAPACITY, INBOX_MIN_DEPOSIT)
}

/// Encode an "outbid" notification payload as a hex-encoded ciphertext bytes string.
///
/// In a real deployment the server would encrypt this with the bidder's public key.
/// For now we use plain bytes; the structure is meaningful to the bidder's client.
pub fn outbid_notification(auction_id_hex: &str, new_high_bid: u64) -> Vec<u8> {
    format!("outbid:{auction_id_hex}:{new_high_bid:016x}")
        .into_bytes()
}

/// Encode a "won" notification payload.
pub fn won_notification(auction_id_hex: &str) -> Vec<u8> {
    format!("won:{auction_id_hex}:claim_within_50_blocks").into_bytes()
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
pub mod tests {
    use axum::body::Body;
    use axum::http::{Method, Request, StatusCode};
    use tower::util::ServiceExt;

    use pyana_app_framework::inbox_endpoint::InboxEndpoint;

    fn hex64(seed: u64) -> String {
        format!("{seed:064x}")
    }

    fn hex_encode_bytes(b: &[u8]) -> String {
        b.iter().map(|byte| format!("{byte:02x}")).collect()
    }

    /// Build a router for isolated testing.
    fn test_router() -> axum::Router {
        InboxEndpoint::new(64, 0).router()
    }

    async fn send_encrypted(
        app: &axum::Router,
        sender_hex: &str,
        ciphertext: &[u8],
    ) -> serde_json::Value {
        let ciphertext_hex = hex_encode_bytes(ciphertext);
        let body = serde_json::json!({
            "sender_hex": sender_hex,
            "deposit": 0u64,
            "ciphertext_hex": ciphertext_hex,
        });
        let resp = app
            .clone()
            .oneshot(
                Request::builder()
                    .method(Method::POST)
                    .uri("/send")
                    .header("content-type", "application/json")
                    .body(Body::from(serde_json::to_vec(&body).unwrap()))
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(resp.status(), StatusCode::OK, "send should succeed");
        let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
            .await
            .unwrap();
        serde_json::from_slice(&bytes).unwrap()
    }

    async fn read_next(app: &axum::Router) -> serde_json::Value {
        let resp = app
            .clone()
            .oneshot(
                Request::builder()
                    .method(Method::GET)
                    .uri("/next")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(resp.status(), StatusCode::OK, "next should succeed");
        let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
            .await
            .unwrap();
        serde_json::from_slice(&bytes).unwrap()
    }

    // -------------------------------------------------------------------------
    // Test 1: outbid notification appears in inbox
    // -------------------------------------------------------------------------

    #[tokio::test]
    async fn outbid_notification_appears_in_inbox() {
        let app = test_router();

        let auction_id = hex64(0xABCD_1234_u64);
        let new_high_bid = 9500_u64;
        let payload = super::outbid_notification(&auction_id, new_high_bid);

        let sender_hex = hex64(0xCAFE_CAFE_CAFE_CAFE_u64);

        // Push notification.
        let send_resp = send_encrypted(&app, &sender_hex, &payload).await;
        assert!(
            send_resp["root_hex"].is_string(),
            "send should return root_hex; got: {send_resp}"
        );

        // Bidder retrieves it.
        let entry = read_next(&app).await;
        assert!(
            entry["sender_hex"].is_string(),
            "entry must have sender_hex; got: {entry}"
        );
        assert_eq!(
            entry["deposit"], 0,
            "deposit should be 0; got: {entry}"
        );
    }

    // -------------------------------------------------------------------------
    // Test 2: winning notification appears in inbox
    // -------------------------------------------------------------------------

    #[tokio::test]
    async fn winning_notification_appears_in_inbox() {
        let app = test_router();

        let auction_id = hex64(0xDEAD_BEEF_u64);
        let payload = super::won_notification(&auction_id);

        let sender_hex = hex64(0xCAFE_CAFE_CAFE_CAFE_u64);

        // Push "you won" notification.
        send_encrypted(&app, &sender_hex, &payload).await;

        // Winner retrieves it.
        let entry = read_next(&app).await;

        // Verify entry fields are present.
        assert!(
            entry["content_hash_hex"].is_string(),
            "entry must have content_hash_hex; got: {entry}"
        );
        // The position should be 0 for the first message.
        assert_eq!(
            entry["position"], 0,
            "first message should be at position 0; got: {entry}"
        );
    }

    // -------------------------------------------------------------------------
    // Test 3: inbox status reflects pending messages count
    // -------------------------------------------------------------------------

    #[tokio::test]
    async fn inbox_status_reflects_pending_count() {
        let app = test_router();

        // Initially empty.
        let status = get_status(&app).await;
        assert_eq!(status["pending_messages"], 0);

        // Push two notifications.
        let sender_hex = hex64(1);
        send_encrypted(&app, &sender_hex, b"outbid:auction1:0000000000002710").await;
        send_encrypted(&app, &sender_hex, b"won:auction2:claim_within_50_blocks").await;

        let status = get_status(&app).await;
        assert_eq!(status["pending_messages"], 2, "should show 2 pending; got: {status}");

        // Read one.
        read_next(&app).await;
        let status = get_status(&app).await;
        assert_eq!(status["pending_messages"], 1, "after reading one, 1 pending; got: {status}");
    }

    async fn get_status(app: &axum::Router) -> serde_json::Value {
        let resp = app
            .clone()
            .oneshot(
                Request::builder()
                    .method(Method::GET)
                    .uri("/status")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(resp.status(), StatusCode::OK);
        let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
            .await
            .unwrap();
        serde_json::from_slice(&bytes).unwrap()
    }
}
