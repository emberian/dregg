//! Blinded-queue bid path for TRUE Vickrey auctions.
//!
//! This module adds a `/queue/bids/*` route backed by a [`FairDistributionEndpoint`],
//! providing strictly stronger privacy than the existing commit-reveal flow:
//!
//! - Bids enter a blinded Merkle queue (the operator never learns intermediate ordering).
//! - Consumption reveals only the nullifier, not the bid ordering observed by the operator.
//! - The existing commit-reveal flow (auction endpoints) is retained as a fallback.
//!
//! # Route summary
//!
//! | Method | Path | Description |
//! |--------|------|-------------|
//! | POST | `/queue/bids/commit` | Submit a bid commitment to the blinded queue |
//! | POST | `/queue/bids/consume` | Consume with a public proof (reveals winner) |
//! | POST | `/queue/bids/consume-private` | Consume with a ZK spending proof (hides ordering) |
//! | GET  | `/queue/bids/status` | Queue status (root, consumed count, remaining) |

use pyana_app_framework::blinded_endpoint::FairDistributionEndpoint;

/// Default capacity of the blinded bid queue (number of bids per auction window).
pub const BLINDED_BID_QUEUE_CAPACITY: usize = 256;

/// Build a fresh [`FairDistributionEndpoint`] for the blinded bid queue.
///
/// The gallery server mounts this at `/queue/bids` via
/// `AppServer::with_blinded_endpoint("/queue/bids", blinded_bid_endpoint())`.
pub fn blinded_bid_endpoint() -> FairDistributionEndpoint {
    FairDistributionEndpoint::new(BLINDED_BID_QUEUE_CAPACITY)
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
pub mod tests {
    use axum::body::Body;
    use axum::http::{Method, Request, StatusCode};
    use tower::util::ServiceExt;

    use pyana_app_framework::blinded_endpoint::FairDistributionEndpoint;

    fn hex64(seed: u64) -> String {
        format!("{seed:064x}")
    }

    /// Build a router for isolated testing.
    fn test_router() -> axum::Router {
        FairDistributionEndpoint::new(16).router()
    }

    // -------------------------------------------------------------------------
    // Test 1: commit followed by public consume succeeds
    // -------------------------------------------------------------------------

    #[tokio::test]
    async fn blinded_bid_commit_and_consume_succeeds() {
        let app = test_router();

        // Step 1: commit a bid.
        let commitment_hex = hex64(0xBEEF_1234_u64);
        let commit_body = serde_json::json!({ "commitment_hex": commitment_hex });
        let resp = app
            .clone()
            .oneshot(
                Request::builder()
                    .method(Method::POST)
                    .uri("/commit")
                    .header("content-type", "application/json")
                    .body(Body::from(serde_json::to_vec(&commit_body).unwrap()))
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(resp.status(), StatusCode::OK, "commit should succeed");

        let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
            .await
            .unwrap();
        let commit_resp: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        assert!(
            commit_resp["root_hex"].is_string(),
            "commit response must have root_hex"
        );

        // Step 2: consume with a public proof.
        // For a single-leaf tree the membership proof is empty and position = 0.
        let nullifier_hex = hex64(0xDEAD_BEEF_u64);
        let consume_body = serde_json::json!({
            "nullifier_hex": nullifier_hex,
            "commitment_hex": commitment_hex,
            "position": 0,
            "membership_proof": []
        });
        let resp = app
            .clone()
            .oneshot(
                Request::builder()
                    .method(Method::POST)
                    .uri("/consume")
                    .header("content-type", "application/json")
                    .body(Body::from(serde_json::to_vec(&consume_body).unwrap()))
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(resp.status(), StatusCode::OK, "consume should return 200");

        let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
            .await
            .unwrap();
        let consume_resp: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        // For a 1-element tree, root = commitment, so empty membership_proof is valid.
        assert_eq!(
            consume_resp["result"], "consumed",
            "consume should succeed for a 1-element queue with empty proof; got: {consume_resp}"
        );
    }

    // -------------------------------------------------------------------------
    // Test 2: double-consume is rejected (nullifier already spent)
    //
    // For a single-element queue the Merkle root IS the commitment, so an empty
    // membership_proof is valid.  The first consume succeeds; the second attempt
    // with the same nullifier is rejected as already_consumed.
    // -------------------------------------------------------------------------

    #[tokio::test]
    async fn blinded_bid_double_consume_rejected() {
        let app = test_router();

        // Commit exactly ONE bid.  For a 1-element tree: root = commitment,
        // so membership_proof = [] is valid.
        let commitment_hex = hex64(0xAAAA_BBBB_u64);
        let body = serde_json::json!({ "commitment_hex": commitment_hex });
        let resp = app
            .clone()
            .oneshot(
                Request::builder()
                    .method(Method::POST)
                    .uri("/commit")
                    .header("content-type", "application/json")
                    .body(Body::from(serde_json::to_vec(&body).unwrap()))
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(resp.status(), StatusCode::OK);

        let nullifier_hex = hex64(0xCAFE_BABE_u64);
        let consume_body = serde_json::json!({
            "nullifier_hex": nullifier_hex,
            "commitment_hex": commitment_hex,
            "position": 0,
            "membership_proof": []
        });

        // First consume — should succeed (valid proof for a 1-item tree).
        let resp = app
            .clone()
            .oneshot(
                Request::builder()
                    .method(Method::POST)
                    .uri("/consume")
                    .header("content-type", "application/json")
                    .body(Body::from(serde_json::to_vec(&consume_body).unwrap()))
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(resp.status(), StatusCode::OK);
        let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
            .await
            .unwrap();
        let first: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(
            first["result"], "consumed",
            "first consume must succeed; got: {first}"
        );

        // Second consume with the SAME nullifier must report already_consumed.
        let resp = app
            .clone()
            .oneshot(
                Request::builder()
                    .method(Method::POST)
                    .uri("/consume")
                    .header("content-type", "application/json")
                    .body(Body::from(serde_json::to_vec(&consume_body).unwrap()))
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(resp.status(), StatusCode::OK);
        let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
            .await
            .unwrap();
        let second: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(
            second["result"], "already_consumed",
            "second consume of same nullifier must be already_consumed; got: {second}"
        );
    }

    // -------------------------------------------------------------------------
    // Test 3: status reports remaining count correctly
    // -------------------------------------------------------------------------

    #[tokio::test]
    async fn blinded_bid_status_reports_remaining() {
        let app = test_router();

        // Initially: 0 committed, capacity 16 → remaining = 0.
        let status = get_status(&app).await;
        assert_eq!(status["remaining"], 0, "empty queue has 0 remaining");
        assert_eq!(status["consumed_count"], 0);

        // After 3 commits: remaining = 3.
        for seed in [0x1111_u64, 0x2222_u64, 0x3333_u64] {
            let body = serde_json::json!({ "commitment_hex": hex64(seed) });
            app.clone()
                .oneshot(
                    Request::builder()
                        .method(Method::POST)
                        .uri("/commit")
                        .header("content-type", "application/json")
                        .body(Body::from(serde_json::to_vec(&body).unwrap()))
                        .unwrap(),
                )
                .await
                .unwrap();
        }

        let status = get_status(&app).await;
        assert_eq!(status["remaining"], 3, "after 3 commits, remaining = 3");
        assert_eq!(status["consumed_count"], 0, "nothing consumed yet");
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
